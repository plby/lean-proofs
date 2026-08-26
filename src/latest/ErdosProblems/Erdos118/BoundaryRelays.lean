import ErdosProblems.Erdos118.ExactSlots
import ErdosProblems.Erdos118.ReservedResponses

/-!
Persistence in the last selected body and exact response fronts at shared
last/first label boundaries. All reserved labels precede their marker;
these operations do not infer coloring invariance under relabeling.
-/

namespace Erdos118.BoundaryRelays

open LabelledExtensions LabelledFrames DecisionStates ReservedResponses LabelOverlays

def SameBody (P Q : Pending) : Prop :=
  Q.roots = [] ∧ Q.position.stem = P.position.stem ∧
    Q.position.size = P.position.size ∧ Q.position.label = P.position.label ∧
    P.position.entries <+: Q.position.entries

private def Remains (P : Pending) : State → Prop
  | .leaf Q => SameBody P Q
  | .complete _ => True
  | _ => False

private theorem remains_step {P : Pending} {S T : State} (hS : Remains P S)
    (h : DecisionStates.Step T S) : Remains P T := by
  cases h with
  | root A => exact hS.elim
  | whole s => exact hS.elim
  | body D A => exact hS.elim
  | leaf F j rest hF A =>
    obtain ⟨hR, hstem, hsize, hlabel, hentries⟩ := hS
    exact ⟨hR, hstem, hsize, hlabel, hentries.trans (List.prefix_append _ _)⟩
  | nextBody F c rest hR hL A =>
    have he : ([] : List ℕ) = c :: rest := hS.1.symm.trans hR
    cases he
  | finish F hR hL A => trivial

theorem run_last_body_left {H : Set ℕ} {payoff : Completed → Completed → Bool}
    (P Q : Pending) (T U : State) (hP : P.roots = [])
    (hrun : ConservativeRuns.Run H payoff (.leaf P, T) (.leaf Q, U)) : SameBody P Q := by
  have hpres : ∀ {V W : State × State}, ConservativeRuns.Run H payoff V W →
      Remains P V.1 → Remains P W.1 := by
    intro V W h
    induction h with
    | refl => exact id
    | tail hprev hstep ih =>
      intro hV
      cases hstep with
      | left n R hs hR a haH hlarge => exact remains_step (ih hV) (R.step a)
      | right n R hs hR a haH hlarge => exact ih hV
  exact hpres hrun ⟨hP, rfl, rfl, rfl, List.prefix_rfl⟩

theorem run_last_body_right {H : Set ℕ} {payoff : Completed → Completed → Bool}
    (P Q : Pending) (S U : State) (hP : P.roots = [])
    (hrun : ConservativeRuns.Run H payoff (S, .leaf P) (U, .leaf Q)) : SameBody P Q := by
  have hpres : ∀ {V W : State × State}, ConservativeRuns.Run H payoff V W →
      Remains P V.2 → Remains P W.2 := by
    intro V W h
    induction h with
    | refl => exact id
    | tail hprev hstep ih =>
      intro hV
      cases hstep with
      | left n R hs hR a haH hlarge => exact ih hV
      | right n R hs hR a haH hlarge => exact remains_step (ih hV) (R.step a)
  exact hpres hrun ⟨hP, rfl, rfl, rfl, List.prefix_rfl⟩

theorem run_last_body_left_cases {H : Set ℕ} {payoff : Completed → Completed → Bool}
    (P : Pending) (T V U : State) (hP : P.roots = [])
    (hrun : ConservativeRuns.Run H payoff (.leaf P, T) (V, U)) :
    (∃ Q : Pending, V = .leaf Q ∧ SameBody P Q) ∨ ∃ C : Completed, V = .complete C := by
  have hpres : ∀ {W Z : State × State}, ConservativeRuns.Run H payoff W Z →
      Remains P W.1 → Remains P Z.1 := by
    intro W Z h
    induction h with
    | refl => exact id
    | tail hprev hstep ih =>
      intro hW
      cases hstep with
      | left n R hs hR a haH hlarge => exact remains_step (ih hW) (R.step a)
      | right n R hs hR a haH hlarge => exact ih hW
  have h := hpres hrun ⟨hP, rfl, rfl, rfl, List.prefix_rfl⟩
  cases V with
  | initial => exact h.elim
  | body D => exact h.elim
  | leaf Q => exact Or.inl ⟨Q, rfl, h⟩
  | complete C => exact Or.inr ⟨C, rfl⟩

theorem body_last_root (D : BodyDecision) (hD : ExactSlots.Exact (.body D))
    (hR : D.roots = []) : D.stem.rootLabel.getLastD 0 = D.stem.done.length + 1 :=
  ExactSlots.last_of_above_empty _ D.stem.label_pairwise D.rootSelected (hD.symm.trans hR)

def rootAtLastBody (D : BodyDecision) (hD : ExactSlots.Exact (.body D))
    (hR : D.roots = []) {l : ℕ} (R : Reserve D.stem.rootLabel D.stem.root l) :
    RootResponses.Setup l :=
  rootSetup D.stem R.label R.increasing R.below l R.card
    ((body_last_root D hD hR).symm.trans R.first.symm)

theorem rootAtLastBody_ordinary (D : BodyDecision) (hD : ExactSlots.Exact (.body D))
    (hR : D.roots = []) {l : ℕ} (R : Reserve D.stem.rootLabel D.stem.root l) :
    (rootAtLastBody D hD hR R).stem.ordinary = D.stem.ordinary :=
  plainStem_ordinary D.stem R.label R.increasing R.below

theorem rootAtLastBody_decorated (D : BodyDecision) (hD : ExactSlots.Exact (.body D))
    (hR : D.roots = []) {l : ℕ} (R : Reserve D.stem.rootLabel D.stem.root l) :
    (rootAtLastBody D hD hR R).stem.decorated = R.label ++ D.stem.ordinary :=
  plainStem_decorated D.stem R.label R.increasing R.below

theorem rootAtLastBody_supported (D : BodyDecision) (hD : ExactSlots.Exact (.body D))
    (hR : D.roots = []) {l : ℕ} (R : Reserve D.stem.rootLabel D.stem.root l)
    {H : Set ℕ} {b : ℕ} (hreserve : ∀ x ∈ R.label, x ∈ H ∧ b < x)
    (hstem : ∀ x ∈ D.stem.ordinary, x ∈ H ∧ b < x) :
    ∀ x ∈ (rootAtLastBody D hD hR R).stem.decorated, x ∈ H ∧ b < x :=
  plainStem_supported D.stem R.label R.increasing R.below hreserve hstem

def bodyAtLastLeaf (P : Pending) (hP : ExactSlots.Exact (.leaf P))
    (hL : P.leaves = []) (C : List ℕ) (hC : C.Pairwise (· < ·))
    (hCr : ∀ x ∈ C, x < P.position.stem.root) {l : ℕ}
    (R : Reserve P.position.label P.position.size l)
    (hbefore : ∀ x ∈ P.position.stem.decorated, ∀ y ∈ R.label, x < y) :
    BodyResponses.Setup (plainStem P.position.stem C hC hCr) l :=
  bodySetup P.position C R.label hC hCr R.increasing R.below
    (before_plain_overlay P.position.stem C R.label hC hCr hbefore) l R.card
    ((ExactSlots.pending_last_leaf P hP hL).symm.trans R.first.symm)

theorem bodyAtLastLeaf_ordinary (P : Pending) (hP : ExactSlots.Exact (.leaf P))
    (hL : P.leaves = []) (C : List ℕ) (hC : C.Pairwise (· < ·))
    (hCr : ∀ x ∈ C, x < P.position.stem.root) {l : ℕ}
    (R : Reserve P.position.label P.position.size l)
    (hbefore : ∀ x ∈ P.position.stem.decorated, ∀ y ∈ R.label, x < y) :
    (bodyAtLastLeaf P hP hL C hC hCr R hbefore).position.ordinary = P.position.ordinary :=
  position_ordinary P.position C R.label hC hCr R.increasing R.below
    (before_plain_overlay P.position.stem C R.label hC hCr hbefore)

theorem bodyAtLastLeaf_newWord (P : Pending) (hP : ExactSlots.Exact (.leaf P))
    (hL : P.leaves = []) (C : List ℕ) (hC : C.Pairwise (· < ·))
    (hCr : ∀ x ∈ C, x < P.position.stem.root) {l : ℕ}
    (R : Reserve P.position.label P.position.size l)
    (hbefore : ∀ x ∈ P.position.stem.decorated, ∀ y ∈ R.label, x < y) :
    BodyResponses.newWord (bodyAtLastLeaf P hP hL C hC hCr R hbefore).position =
      R.label ++ P.position.size :: P.position.entries := rfl

end Erdos118.BoundaryRelays
