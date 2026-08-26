import ErdosProblems.Erdos118.DeferredBodyReplay
import ErdosProblems.Erdos118.FirstBodyRefinement
import ErdosProblems.Erdos118.ManagedRelays

/-!
An opposite word carries the actual initial root reserve until its last
selected body, then a deferred replay to a saved initial root setup.
Right responses preserve this data while the left still needs a body.
-/

namespace Erdos118.DeferredManaged

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses BoundaryRelays PreparedRelays
open ManagedRelays (Initial RootPlan)

inductive Managed {H : Set ℕ} {B : SimpleGraph G} (I : Initial H B .inside) : State → Type
  | body (D : BodyDecision) (root : RootPlan I D.stem) (exactSlots : ExactSlots.Exact (.body D)) :
      Managed I (.body D)
  | waiting (P : Pending) (nonemptyRoots : P.roots ≠ []) (root : RootPlan I P.position.stem)
      (ordinaryFresh : ∀ x ∈ P.position.ordinary, x ∈ H ∧ I.bound < x)
      (exactSlots : ExactSlots.Exact (.leaf P)) : Managed I (.leaf P)
  | prepared (P : Pending) (A : RootResponses.Setup I.size)
      (data : DeferredBodyReplay.Prepared H B .inside false (ofRoot A) .initial P) :
      Managed I (.leaf P)

theorem Managed.exact {H : Set ℕ} {B : SimpleGraph G} {I : Initial H B .inside}
    {S : State} (M : Managed I S) : ExactSlots.Exact S := by
  cases M with
  | body D root h => exact h
  | waiting P hn root hf h => exact h
  | prepared P A Z => exact Z.exactSlots

theorem Managed.working {H : Set ℕ} {B : SimpleGraph G} {I : Initial H B .inside}
    {S : State} (M : Managed I S) : BlueCheckpoints.Working S := by
  cases M <;> trivial

theorem respond_body {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    (I : Initial H B .inside)
    (hfirst : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (FirstBodyRefinement.firstLabel S).length ≠ 1)
    (right : Bool) (D : BodyDecision) (T : State) (root : RootPlan I D.stem)
    (hD : ExactSlots.Exact (.body D))
    (hblue : CommandBlue H B .inside right (.body D) T) :
    ∃ k : ℕ, ∃ A : BodyResponses.Setup D.stem k, ∃ _M : Managed I (.leaf (applyBody D A)),
      ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
        (pair right (.body D) T) (pair right (.leaf (applyBody D A)) T) ∧
      Blue H B .inside right (.leaf (applyBody D A)) T ∧
      OtherBlue H B .inside right (.leaf (applyBody D A)) T := by
  by_cases hR : D.roots = []
  · let C := rootAtLastBody D hD hR root.reserve
    have hf := rootAtLastBody_supported D hD hR root.reserve
      root.reserveFresh root.ordinaryFresh
    have hbC := I.rootBlue C (fun x hx ↦ (hf x hx).1) (fun x hx ↦ (hf x hx).2)
    obtain ⟨l, hl, b, hb⟩ := FirstBodyRefinement.positive_certificate hH B hfirst I.size C hbC
    have hord : (ofRoot C).stem.ordinary = D.stem.ordinary :=
      rootAtLastBody_ordinary D hD hR root.reserve
    obtain ⟨k, A, Z, _, hs, hbA, hh, _⟩ := DeferredBodyReplay.prepare hH Set.Subset.rfl
      B .inside right false D (ofRoot C) T .initial hD hR hord hblue l b hl hb I.bound
    exact ⟨k, A, Managed.prepared (applyBody D A) C Z, hs, hbA, hh⟩
  · obtain ⟨k, A, hs, hb, hh, hf⟩ :=
      PreparedRelays.respond_body hH B .inside right D T hblue I.bound
    let root' : RootPlan I A.position.stem := by rw [A.stem_eq]; exact root
    have hposition : ∀ x ∈ A.position.ordinary, x ∈ H ∧ I.bound < x := by
      rw [BodyResponses.setup_ordinary]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact root.ordinaryFresh x hx
      · exact hf x (List.mem_append_right _ hx)
    exact ⟨k, A, Managed.waiting (applyBody D A) hR root' hposition
      (ExactSlots.step_exact (DecisionStates.Step.body D A) hD), hs, hb, hh⟩

theorem response_ordinary_fresh {H : Set ℕ} {S : State} {b d : ℕ}
    (R : Response S d) (a : R.family.members)
    (hS : ∀ x ∈ S.ordinary, x ∈ H ∧ b < x)
    (ha : ∀ x ∈ a.1, x ∈ H ∧ b < x) :
    ∀ x ∈ (R.result a).ordinary, x ∈ H ∧ b < x := by
  obtain ⟨v, w, hv, hw, _, hvw⟩ := step_extensions (R.step a)
  obtain ⟨u, hu, hua⟩ := R.suffix a
  have hwu : w = u := List.append_cancel_left (hw.symm.trans hu)
  subst u
  rw [hv]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hS x hx
  · exact ha x (hua ▸ List.mem_toFinset.mpr (hvw.subset hx))

private theorem waiting_transition {H : Set ℕ} {B : SimpleGraph G}
    (I : Initial H B .inside) (P : Pending) (hn : P.roots ≠ [])
    (root : RootPlan I P.position.stem) (hP : ExactSlots.Exact (.leaf P))
    {U : State} (hs : DecisionStates.Step U (.leaf P))
    (hf : ∀ x ∈ U.ordinary, x ∈ H ∧ I.bound < x) : Nonempty (Managed I U) := by
  have hU := ExactSlots.step_exact hs hP
  cases hs with
  | leaf F j rest hF A =>
    exact ⟨Managed.waiting (LeafResponses.toPending P j rest hF A) hn root hf hU⟩
  | nextBody F c rest hR hL A =>
    exact ⟨Managed.body (ofStem P c rest hR A)
      (root.transport A.stem A.root_eq A.rootLabel_eq hf) hU⟩
  | finish F hR hL A => exact (hn hR).elim

theorem before_last_not_blue_complete {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (S : State) (hS : BlueCheckpoints.BeforeLastBody S) (C : Completed) :
    ¬ RamseyGame.Outcome H (GraphPayoff.game B .inside (S, .complete C)) true := by
  intro hb
  cases S with
  | initial => exact hS.elim
  | body D => exact body_complete_not_blue hH B .inside D C hb
  | leaf P =>
    exact hS (EndpointOrder.leaf_complete_slots_empty hH B .inside P C hb).1
  | complete D => exact hS.elim

private theorem prepared_right_transition {H : Set ℕ} (hH : H.Infinite)
    {B : SimpleGraph G} (I : Initial H B .inside) (P : Pending)
    (A : RootResponses.Setup I.size)
    (Z : DeferredBodyReplay.Prepared H B .inside false (ofRoot A) .initial P)
    (S : State) (hS : BlueCheckpoints.BeforeLastBody S)
    {U : State} (hs : DecisionStates.Step U (.leaf P))
    (hstep : ConservativeRuns.Step H (GraphPayoff.payoff B .inside) (S, .leaf P) (S, U))
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (S, U)) true) :
    Nonempty (Managed I U) := by
  cases hs with
  | leaf F j rest hF C =>
    obtain ⟨W, _⟩ := DeferredBodyReplay.carry_of_run Z true
      (LeafResponses.toPending P j rest hF C) S S Set.Subset.rfl
      (GraphPayoff.payoff B .inside) (Relation.ReflTransGen.single hstep)
    exact ⟨Managed.prepared _ A W⟩
  | nextBody F c rest hR hL C =>
    have he : ([] : List ℕ) = c :: rest := Z.lastRoot.symm.trans hR
    cases he
  | finish F hR hL C =>
    exact (before_last_not_blue_complete hH B S hS (ofCompletion P C) hblue).elim

theorem respond_right_leaf_with_handoff {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    (I : Initial H B .inside) (P : Pending) (S : State) (M : Managed I (.leaf P))
    (hS : BlueCheckpoints.BeforeLastBody S)
    (hblue : RightBlue H (GraphPayoff.payoff B .inside) (S, .leaf P)) :
    ∃ U : State, Nonempty (Managed I U) ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B .inside) (S, .leaf P) (S, U) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (S, U)) true ∧
      (∀ Q : Pending, U = .leaf Q →
        LeftBlue H (GraphPayoff.payoff B .inside) (S, .leaf Q)) := by
  obtain ⟨R, a, hs, hb, ha⟩ := PreparedRelays.respond hH B .inside true (.leaf P) S hblue I.bound
  refine ⟨R.result a, ?_, hs, hb, ?_⟩
  · cases M with
    | waiting P hn root hf hP =>
      exact waiting_transition I P hn root hP (R.step a) (response_ordinary_fresh R a hf ha)
    | prepared P A Z =>
      exact prepared_right_transition hH I P A Z S hS (R.step a) hs hb
  · intro Q he
    exact handoff_after_right hH B .inside (S, .leaf P) R a Q he (he ▸ hb)

theorem respond_right_leaf {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    (I : Initial H B .inside) (P : Pending) (S : State) (M : Managed I (.leaf P))
    (hS : BlueCheckpoints.BeforeLastBody S)
    (hblue : RightBlue H (GraphPayoff.payoff B .inside) (S, .leaf P)) :
    ∃ U : State, Nonempty (Managed I U) ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B .inside) (S, .leaf P) (S, U) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (S, U)) true := by
  obtain ⟨U, hM, hs, hb, _⟩ := respond_right_leaf_with_handoff hH I P S M hS hblue
  exact ⟨U, hM, hs, hb⟩

theorem respond_right {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    (I : Initial H B .inside)
    (hfirst : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (FirstBodyRefinement.firstLabel S).length ≠ 1)
    (S T : State) (M : Managed I T) (hS : BlueCheckpoints.BeforeLastBody S)
    (hblue : RightBlue H (GraphPayoff.payoff B .inside) (S, T)) :
    ∃ U : State, Nonempty (Managed I U) ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B .inside) (S, T) (S, U) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (S, U)) true := by
  cases M with
  | body D root hD =>
    obtain ⟨k, A, M, hs, hb, _⟩ := respond_body hH I hfirst true D S root hD hblue
    exact ⟨.leaf (applyBody D A), ⟨M⟩, hs, hb⟩
  | waiting P hn root hf hP =>
    exact respond_right_leaf hH I P S (Managed.waiting P hn root hf hP) hS hblue
  | prepared P A Z =>
    exact respond_right_leaf hH I P S (Managed.prepared P A Z) hS hblue

theorem Managed.fire {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    {I : Initial H B .inside} {P : Pending} (M : Managed I (.leaf P))
    (hR : P.roots = []) (hL : P.leaves ≠ []) :
    ∃ Q : Pending, Q.position.ordinary = P.position.ordinary ∧
      Q.position.entries.length = P.position.entries.length ∧
      Q.position.size = P.position.size ∧
      1 < Q.position.label.length ∧
      P.position.label.getLastD 0 ∈ Q.position.label ∧
      (∀ j ∈ Q.position.label, P.position.entries.length < j →
        P.position.label.getLastD 0 ≤ j) ∧
      Q.position.stem.done.length + 1 = Q.position.stem.rootLabel.headD 0 ∧
      Q.position.stem.rootLabel.length = I.size + 1 ∧
      ExactSlots.Exact (.leaf Q) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf Q, .initial)) true ∧
      RightBlue H (GraphPayoff.payoff B .inside) (.leaf Q, .initial) := by
  cases M with
  | waiting P hn root hf hP => exact (hn hR).elim
  | prepared P A Z =>
    obtain ⟨hord, hb, hh⟩ := DeferredBodyReplay.fire hH Z hL
    have hnext := Z.next_index hL
    let Q := applyBody (ofRoot A) (Z.setup hL)
    refine ⟨Q, hord, rfl, rfl, ?_, hnext.2.1, hnext.2.2, ?_, ?_, ?_, hb, hh⟩
    · change Z.label.length > 1
      rw [Z.label_length]
      have h := Z.positive
      omega
    · exact FirstBodyRefinement.first_body I.size Z.size A (Z.setup hL)
    · exact A.label_length
    · exact ExactSlots.step_exact (DecisionStates.Step.body (ofRoot A) (Z.setup hL))
        (ExactSlots.step_exact (DecisionStates.Step.root A) trivial)

end Erdos118.DeferredManaged
