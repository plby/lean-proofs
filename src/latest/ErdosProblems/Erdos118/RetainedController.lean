import ErdosProblems.Erdos118.ReplaySources
import ErdosProblems.Erdos118.BlueCheckpoints

/-!
An actual finite controller for two different concrete certificate sources.
Each source keeps its own bound; all response guards use one fixed working
alphabet. Both preparations are installed before their body markers.
-/

namespace Erdos118.RetainedController

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses BoundaryRelays PreparedRelays ReplaySources

inductive Managed {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {targetRight : Bool} {targetOther : Pending} (I : Source H B o targetRight targetOther) :
    State → Type
  | body (D : BodyDecision) (data : I.Data D.stem) (exactSlots : ExactSlots.Exact (.body D)) :
      Managed I (.body D)
  | waiting (P : Pending) (nonemptyRoots : P.roots ≠ []) (data : I.Data P.position.stem)
      (tailFresh : ∀ x ∈ P.position.size :: P.position.entries, x ∈ H ∧ I.bound < x)
      (exactSlots : ExactSlots.Exact (.leaf P)) : Managed I (.leaf P)
  | prepared (P : Pending) (E : BodyDecision)
      (data : BodyReplay.Prepared H B o targetRight E (.leaf targetOther) P) : Managed I (.leaf P)

theorem Managed.exact {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {targetRight : Bool} {targetOther : Pending} {I : Source H B o targetRight targetOther}
    {S : State} (M : Managed I S) : ExactSlots.Exact S := by
  cases M with
  | body D data h => exact h
  | waiting P hn data hf h => exact h
  | prepared P E Z => exact Z.exactSlots

theorem Managed.working {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {targetRight : Bool} {targetOther : Pending} {I : Source H B o targetRight targetOther}
    {S : State} (M : Managed I S) : BlueCheckpoints.Working S := by
  cases M <;> trivial

theorem respond_body {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    {B : SimpleGraph G} {o : GraphPayoff.Orientation} {targetRight : Bool} {targetOther : Pending}
    (I : Source H B o targetRight targetOther) (right : Bool)
    (D : BodyDecision) (T : State) (data : I.Data D.stem) (hD : ExactSlots.Exact (.body D))
    (hblue : CommandBlue H B o right (.body D) T) :
    ∃ k : ℕ, ∃ A : BodyResponses.Setup D.stem k, ∃ _M : Managed I (.leaf (applyBody D A)),
      ConservativeRuns.Step K (GraphPayoff.payoff B o)
        (pair right (.body D) T) (pair right (.leaf (applyBody D A)) T) ∧
      Blue H B o right (.leaf (applyBody D A)) T ∧
      OtherBlue H B o right (.leaf (applyBody D A)) T := by
  by_cases hR : D.roots = []
  · obtain ⟨E, hord, hc⟩ := I.resolve D data hD hR
    obtain ⟨k, A, Z, hs, hb, hh, _⟩ := BodyReplay.prepare hK hKH B o right targetRight
      D E T (.leaf targetOther) hD hR hord hblue hc I.bound
    exact ⟨k, A, Managed.prepared (applyBody D A) E Z, hs, hb, hh⟩
  · obtain ⟨k, A, hs, hb, hh, hf⟩ :=
      PreparedRelays.respond_body_on hK hKH B o right D T hblue I.bound
    let data' : I.Data A.position.stem := by rw [A.stem_eq]; exact data
    have htail : ∀ x ∈ A.position.size :: A.position.entries, x ∈ H ∧ I.bound < x := by
      intro x hx
      have h := hf x (List.mem_append_right _ hx)
      exact ⟨hKH h.1, h.2⟩
    exact ⟨k, A, Managed.waiting (applyBody D A) hR data' htail
      (ExactSlots.step_exact (DecisionStates.Step.body D A) hD), hs, hb, hh⟩

def BothLast (S : State × State) : Prop :=
  BlueCheckpoints.LastLeaf S.1 ∧ BlueCheckpoints.LastLeaf S.2

private theorem response_suffix_fresh {H : Set ℕ} {S : State} {b d : ℕ}
    (R : Response S d) (a : R.family.members) (ha : ∀ x ∈ a.1, x ∈ H ∧ b < x) :
    ∃ v, (R.result a).ordinary = S.ordinary ++ v ∧ ∀ x ∈ v, x ∈ H ∧ b < x := by
  obtain ⟨v, w, hv, hw, _, hvw⟩ := step_extensions (R.step a)
  obtain ⟨u, hu, hua⟩ := R.suffix a
  have hwu : w = u := List.append_cancel_left (hw.symm.trans hu)
  subst u
  exact ⟨v, hv, fun x hx ↦ ha x (hua ▸ List.mem_toFinset.mpr (hvw.subset hx))⟩

private theorem waiting_transition {H : Set ℕ} {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} {targetRight : Bool} {targetOther : Pending}
    (I : Source H B o targetRight targetOther) (P : Pending) (hn : P.roots ≠ [])
    (data : I.Data P.position.stem)
    (htail : ∀ x ∈ P.position.size :: P.position.entries, x ∈ H ∧ I.bound < x)
    (hP : ExactSlots.Exact (.leaf P)) {U : State} (hs : DecisionStates.Step U (.leaf P))
    (hfresh : ∃ v, U.ordinary = P.position.ordinary ++ v ∧ ∀ x ∈ v, x ∈ H ∧ I.bound < x) :
    Nonempty (Managed I U) := by
  have hU := ExactSlots.step_exact hs hP
  obtain ⟨v, hv, hvf⟩ := hfresh
  cases hs with
  | leaf F j rest hF A =>
    have hslot := P.leafSlots.bounded j (hF ▸ List.mem_cons_self ..)
    have hAv : A.newWord = v := List.append_cancel_left
      ((LeafResponses.position_ordinary A hslot.1 hslot.2.1).symm.trans hv)
    have hf : ∀ x ∈ (P.position.size :: P.position.entries) ++ A.newWord,
        x ∈ H ∧ I.bound < x := by
      intro x hx
      exact (List.mem_append.mp hx).elim (htail x) (fun hx ↦ hvf x (hAv ▸ hx))
    refine ⟨Managed.waiting (LeafResponses.toPending P j rest hF A) hn data ?_ hU⟩
    simpa only [LeafResponses.toPending, LeafResponses.position, List.cons_append] using hf
  | nextBody F c rest hR hL A =>
    have hAv : A.newWord = v := List.append_cancel_left (A.ordinary.symm.trans hv)
    have hord : A.stem.ordinary = P.position.stem.ordinary ++
        ((P.position.size :: P.position.entries) ++ A.newWord) := by
      rw [A.ordinary]
      simp only [Position.ordinary, List.append_assoc]
    have hf : ∀ x ∈ (P.position.size :: P.position.entries) ++ A.newWord,
        x ∈ H ∧ I.bound < x := by
      intro x hx
      exact (List.mem_append.mp hx).elim (htail x) (fun hx ↦ hvf x (hAv ▸ hx))
    exact ⟨Managed.body (ofStem P c rest hR A)
      (data.transport A.stem A.root_eq A.rootLabel_eq _ hord hf) hU⟩
  | finish F hR hL A => exact (hn hR).elim

private theorem other_last_of_complete {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (right : Bool)
    (C : Completed) (T : State) (hT : BlueCheckpoints.Working T)
    (hblue : Blue H B o right (.complete C) T) : BlueCheckpoints.LastLeaf T := by
  cases T with
  | initial => exact hT.elim
  | complete D => exact hT.elim
  | body D =>
    cases right with
    | false => exact (complete_body_not_blue hH B o C D hblue).elim
    | true => exact (body_complete_not_blue hH B o D C hblue).elim
  | leaf P =>
    cases right with
    | false => exact EndpointOrder.complete_leaf_slots_empty hH B o C P hblue
    | true => exact EndpointOrder.leaf_complete_slots_empty hH B o P C hblue

private theorem prepared_transition {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    {B : SimpleGraph G} {o : GraphPayoff.Orientation} {targetRight : Bool} {targetOther : Pending}
    (I : Source H B o targetRight targetOther) (right : Bool) (P : Pending) (E : BodyDecision)
    (Z : BodyReplay.Prepared H B o targetRight E (.leaf targetOther) P)
    (T : State) (hT : BlueCheckpoints.Working T) {U : State}
    (hs : DecisionStates.Step U (.leaf P))
    (hstep : ConservativeRuns.Step K (GraphPayoff.payoff B o)
      (pair right (.leaf P) T) (pair right U T))
    (hblue : Blue H B o right U T) (hnot : ¬ BothLast (pair right (.leaf P) T)) :
    Nonempty (Managed I U) := by
  cases hs with
  | leaf F j rest hF A =>
    obtain ⟨W, _⟩ := BodyReplay.carry_of_run Z right (LeafResponses.toPending P j rest hF A)
      T T hKH (GraphPayoff.payoff B o) (Relation.ReflTransGen.single hstep)
    exact ⟨Managed.prepared _ E W⟩
  | nextBody F c rest hR hL A =>
    have he : ([] : List ℕ) = c :: rest := Z.lastRoot.symm.trans hR
    cases he
  | finish F hR hL A =>
    have hother := other_last_of_complete (hK.mono hKH) B o right (ofCompletion P A) T hT hblue
    apply False.elim
    apply hnot
    cases right with
    | false => exact ⟨⟨hR, hL⟩, hother⟩
    | true => exact ⟨hother, ⟨hR, hL⟩⟩

theorem respond_leaf {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    {B : SimpleGraph G} {o : GraphPayoff.Orientation} {targetRight : Bool} {targetOther : Pending}
    (I : Source H B o targetRight targetOther) (right : Bool) (P : Pending) (T : State)
    (M : Managed I (.leaf P)) (hT : BlueCheckpoints.Working T)
    (hblue : CommandBlue H B o right (.leaf P) T)
    (hnot : ¬ BothLast (pair right (.leaf P) T)) :
    ∃ U : State, Nonempty (Managed I U) ∧
      ConservativeRuns.Step K (GraphPayoff.payoff B o)
        (pair right (.leaf P) T) (pair right U T) ∧ Blue H B o right U T := by
  obtain ⟨R, a, hs, hb, ha⟩ := PreparedRelays.respond_on hK hKH B o right (.leaf P) T hblue I.bound
  refine ⟨R.result a, ?_, hs, hb⟩
  cases M with
  | waiting P hn data hf hP =>
    exact waiting_transition I P hn data hf hP (R.step a)
      (response_suffix_fresh R a (fun x hx ↦ ⟨hKH (ha x hx).1, (ha x hx).2⟩))
  | prepared P E Z => exact prepared_transition hK hKH I right P E Z T hT (R.step a) hs hb hnot

theorem respond_side {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    {B : SimpleGraph G} {o : GraphPayoff.Orientation} {targetRight : Bool} {targetOther : Pending}
    (I : Source H B o targetRight targetOther) (right : Bool) (S T : State)
    (M : Managed I S) (hT : BlueCheckpoints.Working T)
    (hblue : CommandBlue H B o right S T) (hnot : ¬ BothLast (pair right S T)) :
    ∃ U : State, Nonempty (Managed I U) ∧
      ConservativeRuns.Step K (GraphPayoff.payoff B o) (pair right S T) (pair right U T) ∧
      Blue H B o right U T := by
  cases M with
  | body D data hD =>
    obtain ⟨k, A, M, hs, hb, _⟩ := respond_body hK hKH I right D T data hD hblue
    exact ⟨.leaf (applyBody D A), ⟨M⟩, hs, hb⟩
  | waiting P hn data hf hP =>
    exact respond_leaf hK hKH I right P T (Managed.waiting P hn data hf hP) hT hblue hnot
  | prepared P E Z =>
    exact respond_leaf hK hKH I right P T (Managed.prepared P E Z) hT hblue hnot

theorem checkpoint {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    {B : SimpleGraph G} {o : GraphPayoff.Orientation} {r₁ r₂ : Bool} {T₁ T₂ : Pending}
    (I : Source H B o r₁ T₁) (J : Source H B o r₂ T₂) (S : State × State)
    (M : Managed I S.1) (N : Managed J S.2)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o S) true) :
    ∃ V : State × State, ConservativeRuns.Run K (GraphPayoff.payoff B o) S V ∧
      RamseyGame.Outcome H (GraphPayoff.game B o V) true ∧ BothLast V ∧
      Nonempty (Managed I V.1) ∧ Nonempty (Managed J V.2) := by
  induction S using pairStep_wellFounded.induction with
  | h S ih =>
    by_cases hlast : BothLast S
    · exact ⟨S, Relation.ReflTransGen.refl, hblue, hlast, ⟨M⟩, ⟨N⟩⟩
    · have hnone : terminalPayoff (GraphPayoff.payoff B o) S = none := by
        obtain ⟨S, T⟩ := S
        cases M <;> cases N <;> rfl
      rcases blue_command (GraphPayoff.payoff B o) S hnone hblue with hl | hr
      · obtain ⟨U, ⟨M'⟩, hs, hb⟩ := respond_side hK hKH I false S.1 S.2 M N.working hl hlast
        obtain ⟨V, hrun, hbV, hlV, hMV, hNV⟩ := ih (U, S.2) hs.pairStep M' N hb
        exact ⟨V, Relation.ReflTransGen.head hs hrun, hbV, hlV, hMV, hNV⟩
      · obtain ⟨U, ⟨N'⟩, hs, hb⟩ := respond_side hK hKH J true S.2 S.1 N M.working hr hlast
        obtain ⟨V, hrun, hbV, hlV, hMV, hNV⟩ := ih (S.1, U) hs.pairStep M N' hb
        exact ⟨V, Relation.ReflTransGen.head hs hrun, hbV, hlV, hMV, hNV⟩

theorem Managed.fire {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} {targetRight : Bool} {targetOther : Pending}
    {I : Source H B o targetRight targetOther} {P : Pending}
    (M : Managed I (.leaf P)) (hR : P.roots = []) (hL : P.leaves = []) :
    ∃ Q : Pending, Q.position.ordinary = P.position.ordinary ∧
      Blue H B o targetRight (.leaf Q) (.leaf targetOther) ∧
      OtherBlue H B o targetRight (.leaf Q) (.leaf targetOther) := by
  cases M with
  | waiting P hn data hf hP => exact (hn hR).elim
  | prepared P E Z =>
    have h := BodyReplay.fire hH Z hL
    exact ⟨applyBody E (Z.setup hL), h.1, h.2.1, h.2.2⟩

end Erdos118.RetainedController
