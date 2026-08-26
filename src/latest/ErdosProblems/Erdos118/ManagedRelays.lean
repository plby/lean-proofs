import ErdosProblems.Erdos118.PreparedRelays
import ErdosProblems.Erdos118.BlueCheckpoints

/-!
The invariant for coupled relay construction. Before the last selected
body, retain the root reserve; in the last body, retain a prepared relay.
The initial-root certificate is fixed before any of these responses.
-/

namespace Erdos118.ManagedRelays

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses BoundaryRelays

structure Initial (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation) where
  size : ℕ
  bound : ℕ
  rootBlue : ∀ A : RootResponses.Setup size,
    (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, bound < x) →
    RamseyGame.Outcome H (GraphPayoff.game B o (.body (ofRoot A), .initial)) true

theorem exists_initial {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3) (o : GraphPayoff.Orientation)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.initial, .initial)) true) :
    Nonempty (Initial H B o) := by
  obtain ⟨k, b, hb⟩ := BlueReservations.initial_root_setups hH B hB o hblue
  exact ⟨⟨k, b, hb⟩⟩

structure RootPlan {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    (I : Initial H B o) (S : Stem) where
  reserve : Reserve S.rootLabel S.root I.size
  reserveFresh : ∀ x ∈ reserve.label, x ∈ H ∧ I.bound < x
  ordinaryFresh : ∀ x ∈ S.ordinary, x ∈ H ∧ I.bound < x

def RootPlan.transport {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {I : Initial H B o} {S : Stem} (R : RootPlan I S) (U : Stem)
    (hroot : U.root = S.root) (hlabel : U.rootLabel = S.rootLabel)
    (hfresh : ∀ x ∈ U.ordinary, x ∈ H ∧ I.bound < x) : RootPlan I U where
  reserve :=
    { label := R.reserve.label, card := R.reserve.card, increasing := R.reserve.increasing
      first := by rw [hlabel]; exact R.reserve.first
      below := by rw [hroot]; exact R.reserve.below
      shared := by intro x; rw [hlabel]; exact R.reserve.shared x }
  reserveFresh := R.reserveFresh
  ordinaryFresh := hfresh

inductive Managed {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    (I : Initial H B o) : State → Type
  | body (D : BodyDecision) (root : RootPlan I D.stem) (exactSlots : ExactSlots.Exact (.body D)) :
      Managed I (.body D)
  | waiting (P : Pending) (nonemptyRoots : P.roots ≠ []) (root : RootPlan I P.position.stem)
      (ordinaryFresh : ∀ x ∈ P.position.ordinary, x ∈ H ∧ I.bound < x)
      (exactSlots : ExactSlots.Exact (.leaf P)) : Managed I (.leaf P)
  | prepared (P : Pending) (E : BodyDecision)
      (data : PreparedRelays.Prepared H B o false E .initial P) : Managed I (.leaf P)

theorem Managed.exact {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {I : Initial H B o} {S : State} (M : Managed I S) : ExactSlots.Exact S := by
  cases M with
  | body D root h => exact h
  | waiting P hn root hf h => exact h
  | prepared P E Z => exact Z.exactSlots

theorem Managed.working {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {I : Initial H B o} {S : State} (M : Managed I S) : BlueCheckpoints.Working S := by
  cases M <;> trivial

theorem respond_body {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} (I : Initial H B o) (right : Bool)
    (D : BodyDecision) (T : State) (root : RootPlan I D.stem)
    (hD : ExactSlots.Exact (.body D))
    (hblue : PreparedRelays.CommandBlue H B o right (.body D) T) :
    ∃ k : ℕ, ∃ A : BodyResponses.Setup D.stem k, ∃ _M : Managed I (.leaf (applyBody D A)),
      ConservativeRuns.Step H (GraphPayoff.payoff B o)
        (PreparedRelays.pair right (.body D) T)
        (PreparedRelays.pair right (.leaf (applyBody D A)) T) ∧
      PreparedRelays.Blue H B o right (.leaf (applyBody D A)) T ∧
      PreparedRelays.OtherBlue H B o right (.leaf (applyBody D A)) T := by
  by_cases hR : D.roots = []
  · let E := ofRoot (rootAtLastBody D hD hR root.reserve)
    have hfresh := rootAtLastBody_supported D hD hR root.reserve
      root.reserveFresh root.ordinaryFresh
    have hsecond := I.rootBlue (rootAtLastBody D hD hR root.reserve)
      (fun x hx ↦ (hfresh x hx).1) (fun x hx ↦ (hfresh x hx).2)
    have hcommand : PreparedRelays.CommandBlue H B o false (.body E) .initial := by
      rcases blue_command (GraphPayoff.payoff B o) (.body E, .initial) rfl hsecond with hl | hr
      · exact hl
      · obtain ⟨n, R, hs, _⟩ := hr
        simp [allowedSide] at hs
    obtain ⟨k, A, Z, hs, hb, hh, _⟩ := PreparedRelays.prepare hH (Set.Subset.rfl)
      B o right false D E T .initial hD hR root.reserve.label root.reserve.increasing
      root.reserve.below rfl hblue hcommand I.bound
    exact ⟨k, A, Managed.prepared (applyBody D A) E Z, hs, hb, hh⟩
  · obtain ⟨k, A, hs, hb, hh, hfresh⟩ :=
      PreparedRelays.respond_body hH B o right D T hblue I.bound
    let root' : RootPlan I A.position.stem := by rw [A.stem_eq]; exact root
    have hposition : ∀ x ∈ A.position.ordinary, x ∈ H ∧ I.bound < x := by
      rw [BodyResponses.setup_ordinary]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact root.ordinaryFresh x hx
      · exact hfresh x (List.mem_append_right _ hx)
    exact ⟨k, A, Managed.waiting (applyBody D A) hR root' hposition
      (ExactSlots.step_exact (DecisionStates.Step.body D A) hD), hs, hb, hh⟩

def BothLast (S : State × State) : Prop :=
  BlueCheckpoints.LastLeaf S.1 ∧ BlueCheckpoints.LastLeaf S.2

private theorem response_ordinary_fresh {H : Set ℕ} {S : State} {b d : ℕ}
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
    {o : GraphPayoff.Orientation} (I : Initial H B o) (P : Pending)
    (hn : P.roots ≠ []) (root : RootPlan I P.position.stem)
    (hP : ExactSlots.Exact (.leaf P)) {U : State} (hs : DecisionStates.Step U (.leaf P))
    (hfresh : ∀ x ∈ U.ordinary, x ∈ H ∧ I.bound < x) : Nonempty (Managed I U) := by
  have hU := ExactSlots.step_exact hs hP
  cases hs with
  | leaf F j rest hF A =>
    exact ⟨Managed.waiting (LeafResponses.toPending P j rest hF A) hn root hfresh hU⟩
  | nextBody F c rest hR hL A =>
    exact ⟨Managed.body (ofStem P c rest hR A)
      (root.transport A.stem A.root_eq A.rootLabel_eq hfresh) hU⟩
  | finish F hR hL A => exact (hn hR).elim

private theorem other_last_of_complete {H : Set ℕ} (hH : H.Infinite)
    {B : SimpleGraph G} {o : GraphPayoff.Orientation} (I : Initial H B o)
    (right : Bool) (C : Completed) (T : State) (M : Managed I T)
    (hblue : PreparedRelays.Blue H B o right (.complete C) T) : BlueCheckpoints.LastLeaf T := by
  cases right with
  | false =>
    cases M with
    | body D root hD => exact (complete_body_not_blue hH B o C D hblue).elim
    | waiting P hn root hf hP => exact EndpointOrder.complete_leaf_slots_empty hH B o C P hblue
    | prepared P E Z => exact EndpointOrder.complete_leaf_slots_empty hH B o C P hblue
  | true =>
    cases M with
    | body D root hD => exact (body_complete_not_blue hH B o D C hblue).elim
    | waiting P hn root hf hP => exact EndpointOrder.leaf_complete_slots_empty hH B o P C hblue
    | prepared P E Z => exact EndpointOrder.leaf_complete_slots_empty hH B o P C hblue

private theorem prepared_transition {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} (I : Initial H B o) (right : Bool)
    (P : Pending) (E : BodyDecision) (Z : PreparedRelays.Prepared H B o false E .initial P)
    (T : State) (M : Managed I T) {U : State} (hs : DecisionStates.Step U (.leaf P))
    (hstep : ConservativeRuns.Step H (GraphPayoff.payoff B o)
      (PreparedRelays.pair right (.leaf P) T) (PreparedRelays.pair right U T))
    (hblue : PreparedRelays.Blue H B o right U T)
    (hnot : ¬ BothLast (PreparedRelays.pair right (.leaf P) T)) : Nonempty (Managed I U) := by
  cases hs with
  | leaf F j rest hF A =>
    have hrun := Relation.ReflTransGen.single hstep
    cases right with
    | false =>
      obtain ⟨W, _⟩ := PreparedRelays.carry_left Z (LeafResponses.toPending P j rest hF A)
        T T M.exact (Set.Subset.rfl) (GraphPayoff.payoff B o) hrun
      exact ⟨Managed.prepared _ E W⟩
    | true =>
      obtain ⟨W, _⟩ := PreparedRelays.carry_right Z (LeafResponses.toPending P j rest hF A)
        T T M.exact (Set.Subset.rfl) (GraphPayoff.payoff B o) hrun
      exact ⟨Managed.prepared _ E W⟩
  | nextBody F c rest hR hL A =>
    have he : ([] : List ℕ) = c :: rest := Z.lastRoot.symm.trans hR
    cases he
  | finish F hR hL A =>
    have hother := other_last_of_complete hH I right (ofCompletion P A) T M hblue
    apply False.elim
    apply hnot
    cases right with
    | false => exact ⟨⟨hR, hL⟩, hother⟩
    | true => exact ⟨hother, ⟨hR, hL⟩⟩

theorem respond_leaf {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} (I : Initial H B o) (right : Bool)
    (P : Pending) (T : State) (M : Managed I (.leaf P)) (MT : Managed I T)
    (hblue : PreparedRelays.CommandBlue H B o right (.leaf P) T)
    (hnot : ¬ BothLast (PreparedRelays.pair right (.leaf P) T)) :
    ∃ U : State, Nonempty (Managed I U) ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B o)
        (PreparedRelays.pair right (.leaf P) T) (PreparedRelays.pair right U T) ∧
      PreparedRelays.Blue H B o right U T := by
  obtain ⟨R, a, hs, hb, ha⟩ := PreparedRelays.respond hH B o right (.leaf P) T hblue I.bound
  refine ⟨R.result a, ?_, hs, hb⟩
  cases M with
  | waiting P hn root hf hP =>
    exact waiting_transition I P hn root hP (R.step a) (response_ordinary_fresh R a hf ha)
  | prepared P E Z =>
    exact prepared_transition hH I right P E Z T MT (R.step a) hs hb hnot

theorem respond_side {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} (I : Initial H B o) (right : Bool)
    (S T : State) (M : Managed I S) (MT : Managed I T)
    (hblue : PreparedRelays.CommandBlue H B o right S T)
    (hnot : ¬ BothLast (PreparedRelays.pair right S T)) :
    ∃ U : State, Nonempty (Managed I U) ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B o)
        (PreparedRelays.pair right S T) (PreparedRelays.pair right U T) ∧
      PreparedRelays.Blue H B o right U T := by
  cases M with
  | body D root hD =>
    obtain ⟨k, A, M, hs, hb, _⟩ := respond_body hH I right D T root hD hblue
    exact ⟨.leaf (applyBody D A), ⟨M⟩, hs, hb⟩
  | waiting P hn root hf hP =>
    exact respond_leaf hH I right P T (Managed.waiting P hn root hf hP) MT hblue hnot
  | prepared P E Z =>
    exact respond_leaf hH I right P T (Managed.prepared P E Z) MT hblue hnot

theorem Managed.fire {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G}
    {o : GraphPayoff.Orientation} {I : Initial H B o} {P : Pending}
    (M : Managed I (.leaf P)) (hR : P.roots = []) (hL : P.leaves = []) :
    ∃ Q : Pending, Q.position.ordinary = P.position.ordinary ∧
      RamseyGame.Outcome H (GraphPayoff.game B o (.leaf Q, .initial)) true ∧
      RightBlue H (GraphPayoff.payoff B o) (.leaf Q, .initial) := by
  cases M with
  | waiting P hn root hf hP => exact (hn hR).elim
  | prepared P E Z =>
    have h := PreparedRelays.fire hH Z hL
    exact ⟨applyBody E (Z.setup hL), h.1, h.2.1, h.2.2⟩

end Erdos118.ManagedRelays
