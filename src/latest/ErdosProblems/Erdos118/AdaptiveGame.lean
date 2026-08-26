import ErdosProblems.Erdos118.DecisionStates

/-!
An actual adaptive Ramsey game built by well-founded recursion on concrete
decision states. The terminal payoff is a parameter; no clear-pair graph
payoff or blue-to-triangle implication is assumed or asserted here.
-/

namespace Erdos118.AdaptiveGame

open LabelledExtensions LabelledFrames DecisionStates Negative Negative.Exact Erdos590.Larson

def afterBound (F : RamseyGame.ResponseFamily) (b : ℕ) : RamseyGame.ResponseFamily where
  members := {s | s ∈ F.members ∧ ∀ x ∈ s, b < x}
  thin := by
    intro s hs t ht hst
    exact F.thin hs.1 ht.1 hst
  hits := by
    intro H hH
    obtain ⟨s, hsH, hslarge⟩ := F.conservative_exists hH b
    exact ⟨s.1, ⟨s.2, hslarge⟩, hsH⟩

def forgetBound (F : RamseyGame.ResponseFamily) (b : ℕ) :
    (afterBound F b).members → F.members := fun a ↦ ⟨a.1, a.2.1⟩

@[simp] theorem forgetBound_value (F : RamseyGame.ResponseFamily) (b : ℕ)
    (a : (afterBound F b).members) : (forgetBound F b a).1 = a.1 := rfl

theorem afterBound_large (F : RamseyGame.ResponseFamily) (b : ℕ)
    (a : (afterBound F b).members) : ∀ x ∈ a.1, b < x := a.2.2

structure Response (S : State) (b : ℕ) where
  family : RamseyGame.ResponseFamily
  result : family.members → State
  step : ∀ a, Step (result a) S
  suffix : ∀ a, ∃ d : List ℕ, (result a).decorated = S.decorated ++ d ∧ d.toFinset = a.1
  large : ∀ a : family.members, ∀ x ∈ a.1, b < x

noncomputable def ofFront {X : Type} (S : State) (b : ℕ) (F : RamseyGame.ResponseFamily)
    (e : X ≃ F.members) (word : X → List ℕ)
    (support_eq : ∀ x, (word x).toFinset = (e x).1)
    (result : X → State) (step : ∀ x, Step (result x) S)
    (suffix : ∀ x, (result x).decorated = S.decorated ++ word x) : Response S b where
  family := afterBound F b
  result := fun a ↦ result (e.symm (forgetBound F b a))
  step := fun a ↦ step _
  suffix := by
    intro a
    refine ⟨word (e.symm (forgetBound F b a)), suffix _, ?_⟩
    rw [support_eq, e.apply_symm_apply]
    rfl
  large := afterBound_large F b

theorem Response.fresh_suffix {S : State} {b : ℕ} (R : Response S b)
    (a : R.family.members) {H : Set ℕ} (ha : (↑a.1 : Set ℕ) ⊆ H) :
    ∃ d : List ℕ, (R.result a).decorated = S.decorated ++ d ∧
      ∀ x ∈ d, x ∈ H ∧ b < x := by
  obtain ⟨d, hd, hs⟩ := R.suffix a
  refine ⟨d, hd, ?_⟩
  intro x hx
  have hxa : x ∈ a.1 := hs ▸ List.mem_toFinset.mpr hx
  exact ⟨ha hxa, R.large a x hxa⟩

noncomputable def rootResponse (k b : ℕ) : Response .initial b :=
  ofFront .initial b (RootResponses.responseFamily k) (RootResponses.supportEquiv k)
    (fun A ↦ A.stem.decorated) (fun _ ↦ rfl)
    (fun A ↦ .body (ofRoot A)) (fun A ↦ Step.root A) (fun _ ↦ rfl)

noncomputable def wholeResponse (b : ℕ) : Response .initial b :=
  ofFront .initial b WordResponses.responseFamily WordResponses.supportEquiv
    (fun s ↦ word s.1) (fun _ ↦ rfl)
    (fun s ↦ .complete (ofGood s)) (fun s ↦ Step.whole s) ofGood_decorated

noncomputable def bodyResponse (D : BodyDecision) (k b : ℕ) : Response (.body D) b :=
  ofFront (.body D) b (BodyResponses.responseFamily D.stem k D.room)
    (BodyResponses.supportEquiv D.stem k) (fun A ↦ BodyResponses.newWord A.position)
    (fun _ ↦ rfl) (fun A ↦ .leaf (applyBody D A)) (fun A ↦ Step.body D A)
    BodyResponses.setup_decorated

noncomputable def leafResponse (F : Pending) (j : ℕ) (rest : List ℕ)
    (hF : F.leaves = j :: rest) (b : ℕ) : Response (.leaf F) b := by
  have hslot := F.leafSlots.bounded j (hF ▸ List.mem_cons_self ..)
  exact ofFront (.leaf F) b (LeafResponses.responseFamily F.position j)
    (LeafResponses.supportEquiv F.position j) (fun A ↦ A.newWord)
    (fun _ ↦ rfl) (fun A ↦ .leaf (LeafResponses.toPending F j rest hF A))
    (fun A ↦ Step.leaf F j rest hF A)
    (fun A ↦ LeafResponses.position_decorated A hslot.1 hslot.2.1)

noncomputable def nextBodyResponse (F : Pending) (c : ℕ) (rest : List ℕ)
    (hR : F.roots = c :: rest) (hL : F.leaves = []) (b : ℕ) : Response (.leaf F) b := by
  have hb := next_body_bounds F c rest hR
  exact ofFront (.leaf F) b (StemResponses.responseFamily F.position (c - 1) hb.1 hb.2.1)
    (StemResponses.supportEquiv F.position (c - 1)) (fun A ↦ A.newWord)
    (fun _ ↦ rfl) (fun A ↦ .body (ofStem F c rest hR A))
    (fun A ↦ Step.nextBody F c rest hR hL A) (fun A ↦ A.decorated)

noncomputable def finishResponse (F : Pending) (hR : F.roots = []) (hL : F.leaves = [])
    (b : ℕ) : Response (.leaf F) b := by
  have hpm : F.position.stem.done.length < F.position.stem.root := by
    have h := F.position.room
    omega
  exact ofFront (.leaf F) b
    (StemResponses.responseFamily F.position F.position.stem.root hpm le_rfl)
    (StemResponses.supportEquiv F.position F.position.stem.root) (fun A ↦ A.newWord)
    (fun _ ↦ rfl) (fun A ↦ .complete (ofCompletion F A))
    (fun A ↦ Step.finish F hR hL A) (fun A ↦ A.decorated)

/-- At an initial state zero requests whole completion; successor commands
request a positive root-label cardinality. At a body decision the command
chooses the label cardinality minus one. Leaf responses are determined by
the unused slots. -/
noncomputable def responseFor (S : State) (b n : ℕ) : Option (Response S b) := by
  cases S with
  | initial =>
    cases n with
    | zero => exact some (wholeResponse b)
    | succ k => exact some (rootResponse k b)
  | body D => exact some (bodyResponse D n b)
  | leaf F =>
    exact match hL : F.leaves with
      | j :: rest => some (leafResponse F j rest hL b)
      | [] => match hR : F.roots with
        | c :: rest => some (nextBodyResponse F c rest hR hL b)
        | [] => some (finishResponse F hR hL b)
  | complete T => exact none

def pairBound (S : State × State) : ℕ := max S.1.decorated.sum S.2.decorated.sum

theorem pairBound_left (S : State × State) {x : ℕ} (hx : x ∈ S.1.decorated) :
    x ≤ pairBound S := (nat_le_sum_of_mem hx).trans (le_max_left _ _)

theorem pairBound_right (S : State × State) {x : ℕ} (hx : x ∈ S.2.decorated) :
    x ≤ pairBound S := (nat_le_sum_of_mem hx).trans (le_max_right _ _)

def terminalPayoff (payoff : Completed → Completed → Bool) (S : State × State) : Option Bool :=
  match S.1, S.2 with
  | .complete T, .complete U => some (payoff T U)
  | _, _ => none

/-- A body decision must continue on its own word; initially the first word
must be started first. The first branch also specifies a total behavior on
the case of two simultaneous body decisions. -/
def allowedSide (S : State × State) (right : Bool) : Bool :=
  match S.1, S.2 with
  | .body _, _ => !right
  | _, .body _ => right
  | .initial, .initial => !right
  | _, _ => true

noncomputable def build (payoff : Completed → Completed → Bool) (S : State × State)
    (rec : ∀ T, PairStep T S → RamseyGame.Game) : RamseyGame.Game :=
  match terminalPayoff payoff S with
  | some value => .leaf value
  | none => .choice fun n ↦
    if n % 2 = 0 then
      if allowedSide S false then
        match responseFor S.1 (pairBound S) (n / 2) with
        | none => .leaf false
        | some R => .response R.family fun a ↦ rec (R.result a, S.2) (PairStep.left S.2 (R.step a))
      else .leaf false
    else
      if allowedSide S true then
        match responseFor S.2 (pairBound S) (n / 2) with
        | none => .leaf false
        | some R => .response R.family fun a ↦ rec (S.1, R.result a) (PairStep.right S.1 (R.step a))
      else .leaf false

noncomputable def game (payoff : Completed → Completed → Bool) :
    (State × State) → RamseyGame.Game := pairStep_wellFounded.fix (build payoff)

theorem game_eq (payoff : Completed → Completed → Bool) (S : State × State) :
    game payoff S = build payoff S (fun T _ ↦ game payoff T) := by
  unfold game
  exact WellFounded.fix_eq _ _ _

theorem game_complete (payoff : Completed → Completed → Bool) (T U : Completed) :
    game payoff (.complete T, .complete U) = .leaf (payoff T U) := by
  rw [game_eq]
  rfl

theorem responseFor_none_iff (S : State) (b n : ℕ) :
    responseFor S b n = none ↔ ∃ T : Completed, S = .complete T := by
  cases S with
  | initial => cases n <;> simp [responseFor]
  | body D => simp [responseFor]
  | leaf F =>
    constructor
    · intro h
      dsimp only [responseFor] at h
      split at h
      · cases h
      · split at h <;> cases h
    · rintro ⟨T, hT⟩
      cases hT
  | complete T => simp [responseFor]

theorem responseFor_available (S : State) (b n c : ℕ)
    (hS : ¬ ∃ T : Completed, S = .complete T) {H : Set ℕ} (hH : H.Infinite) :
    ∃ R : Response S b, responseFor S b n = some R ∧
      ∃ a : R.family.members, (↑a.1 : Set ℕ) ⊆ H ∧ ∀ x ∈ a.1, max b c < x := by
  cases hR : responseFor S b n with
  | none => exact (hS ((responseFor_none_iff S b n).mp hR)).elim
  | some R =>
    obtain ⟨a, haH, halarge⟩ := R.family.conservative_exists hH (max b c)
    exact ⟨R, rfl, a, haH, halarge⟩

theorem outcome_thinning (payoff : Completed → Completed → Bool) (S : State × State)
    {N : Set ℕ} (hN : N.Infinite) :
    ∃ H ⊆ N, H.Infinite ∧ ∃ value, RamseyGame.Outcome H (game payoff S) value :=
  RamseyGame.dichotomy (game payoff S) N hN

end Erdos118.AdaptiveGame
