import ErdosProblems.Erdos118.StrictLastMarkerBridge
import ErdosProblems.Erdos118.FutureAnchorBounds
import ErdosProblems.Erdos118.FixedLeftBodyRefinement

/-! Localize the future spliced anchor label while preserving the
already issued target last-body parameter and both paused source words. -/

namespace Erdos118.StrictAnchorLocalization

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open BlueRuns LastBodyRefinement InsideCounts

def anchorSize {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {J : StrictTwoRootRequests.Requests O true} (W : StrictSecondOpening.Opening J)
    (T : Completed) : ℕ :=
  (T.stem.bodyLabels.getD (W.reserve.labels.next - 1) []).length

private theorem terminal_bound {H : Set ℕ} {B : SimpleGraph G}
    {O : StrictInitialOpening.Opening H B} {J : StrictTwoRootRequests.Requests O true}
    (W : StrictSecondOpening.Opening J) (hanchor : W.anchorRank = J.rank + 1)
    (hstrict : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T)
    (S T : Completed) (hp : GraphPayoff.payoff J.graph .inside S T = true)
    (hS : 1 < S.stem.rootLabel.length) (hT : T.stem.rootLabel = W.reserve.labels.upper) :
    0 < anchorSize W T ∧ anchorSize W T + 2 ≤ (lastLabel S).length := by
  have hpB := LastMarkerRefinement.payoff_true_mono J.subgraph .inside S T hp
  have hc := ((GraphPayoff.payoff_true_iff J.graph .inside S T).mp hp).2.1
  have hs := (StrictCriticalBounds.terminal B S T hpB hS (hstrict S T hpB)).2.1
  have hlen : T.stem.rootLabel.length = J.upper.size + 1 := by
    rw [hT, W.reserve.labels.upperCard]
  have hr := (J.exactRank S T hp hS hlen).1
  have hrank : CriticalPair.bodyRank T.stem (lastLabel S).length + 1 = W.anchorRank := by
    rw [hr, hanchor]
  have hbound : W.anchorRank < J.upper.size + 1 := by
    rw [hanchor]
    exact J.lastBound rfl
  exact FutureAnchorBounds.spliced_anchor W.reserve.labels hbound T S.stem
    hc.exactRight hT hs hrank

structure Localized {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {J : StrictTwoRootRequests.Requests O true} {W : StrictSecondOpening.Opening J}
    {Q : StrictSharedBodyRequests.Requests W} {F : StrictSharedFirstLeaves.Pair Q}
    {R : StrictMarkerRequests.Requests F} (D : StrictLastMarkerBridge.Diagram R) where
  alphabet : Set ℕ
  subset : alphabet ⊆ W.prepared.alphabet
  infinite : alphabet.Infinite
  graph : SimpleGraph G
  subgraph : graph ≤ J.graph
  triangleFree : graph.CliqueFree 3
  command : LeftBlue alphabet (GraphPayoff.payoff graph .inside)
    (.body D.bridge.target, .leaf D.checkpoint.right)
  bound : ℕ
  certificate : ∀ A : BodyResponses.Setup D.bridge.target.stem D.targetRequest.size,
    (∀ x ∈ BodyResponses.newWord A.position, x ∈ alphabet) →
    (∀ x ∈ BodyResponses.newWord A.position, bound < x) →
    RamseyGame.Outcome alphabet (GraphPayoff.game graph .inside
      (.leaf (applyBody D.bridge.target A), .leaf D.checkpoint.right)) true
  size : ℕ
  positive : 0 < size
  slack : size + 2 ≤ D.targetRequest.size + 1
  fixed : ∀ S T : Completed, GraphPayoff.payoff graph .inside S T = true →
    min (anchorSize W T) (D.targetRequest.size + 1) = size
  exactSize : ∀ S T : Completed, GraphPayoff.payoff graph .inside S T = true →
    1 < S.stem.rootLabel.length → T.stem.rootLabel = W.reserve.labels.upper →
    (lastLabel S).length = D.targetRequest.size + 1 → anchorSize W T = size

theorem exists_localized {H : Set ℕ} {B : SimpleGraph G}
    {O : StrictInitialOpening.Opening H B} {J : StrictTwoRootRequests.Requests O true}
    {W : StrictSecondOpening.Opening J} {Q : StrictSharedBodyRequests.Requests W}
    {F : StrictSharedFirstLeaves.Pair Q} {R : StrictMarkerRequests.Requests F}
    (D : StrictLastMarkerBridge.Diagram R) (hanchor : W.anchorRank = J.rank + 1)
    (hstrict : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T) : Nonempty (Localized D) := by
  obtain ⟨L, hLK, hL, C, hCJ, hC, hcommand, a, _, d, hcert, htest⟩ :=
    FixedLeftBodyRefinement.refine W.prepared.infinite J.graph J.triangleFree
      D.bridge.target D.checkpoint.right D.targetRequest.size D.targetRequest.bound
      D.targetRequest.certificate (D.targetRequest.size + 1)
      (fun _ T ↦ min (anchorSize W T) (D.targetRequest.size + 1))
      (fun _ _ _ ↦ min_le_right _ _)
  have hexact : ∀ S T : Completed, GraphPayoff.payoff C .inside S T = true →
      1 < S.stem.rootLabel.length → T.stem.rootLabel = W.reserve.labels.upper →
      (lastLabel S).length = D.targetRequest.size + 1 → anchorSize W T = a := by
    intro S T hp hS hT hlast
    have hb := terminal_bound W hanchor hstrict S T
      (LastMarkerRefinement.payoff_true_mono hCJ .inside S T hp) hS hT
    have hle : anchorSize W T ≤ D.targetRequest.size + 1 := by omega
    simpa only [min_eq_left hle] using htest S T hp
  obtain ⟨A, hA⟩ := BodyResponses.setup_above D.bridge.target.stem D.targetRequest.size
    D.bridge.target.room hL d
  have hblue := hcert A (fun x hx ↦ (hA x hx).1) (fun x hx ↦ (hA x hx).2)
  obtain ⟨S, T, hrun, hp⟩ := blue_completion hL (GraphPayoff.payoff C .inside)
    (.leaf (applyBody D.bridge.target A), .leaf D.checkpoint.right) hblue
  have he := SkippedCuts.run_extensions hrun
  have hDroot : D.bridge.target.stem.rootLabel = O.reserve.labels.upper := by
    have hstep := (SkippedCuts.run_extensions
      (Relation.ReflTransGen.single D.bridge.targetStep)).1
    exact (Option.some.inj (hstep.labels.root _ rfl)).trans D.checkpoint.leftRoot
  have hSroot : S.stem.rootLabel = O.reserve.labels.upper := by
    have hroot : S.stem.rootLabel = A.position.stem.rootLabel :=
      Option.some.inj (he.1.labels.root _ rfl)
    rw [A.stem_eq] at hroot
    exact hroot.trans hDroot
  have hS : 1 < S.stem.rootLabel.length := by
    rw [hSroot, O.reserve.labels.upperCard]
    have hpos := O.positive
    omega
  have hT : T.stem.rootLabel = W.reserve.labels.upper :=
    (Option.some.inj (he.2.labels.root _ rfl)).trans D.checkpoint.rightRoot
  have hlabel := lastLabel_of_extension (applyBody D.bridge.target A) S
    (ExactSlots.step_exact (DecisionStates.Step.body D.bridge.target A) D.bridge.targetExact)
    D.bridge.targetRoots he.1.labels
  have hlast : (lastLabel S).length = D.targetRequest.size + 1 := by
    rw [hlabel]
    exact A.label_length
  have hb := terminal_bound W hanchor hstrict S T
    (LastMarkerRefinement.payoff_true_mono hCJ .inside S T hp) hS hT
  rw [hexact S T hp hS hT hlast, hlast] at hb
  exact ⟨{
    alphabet := L, subset := hLK, infinite := hL, graph := C, subgraph := hCJ
    triangleFree := hC, command := hcommand, bound := d, certificate := hcert
    size := a, positive := hb.1, slack := hb.2, fixed := htest, exactSize := hexact }⟩

end Erdos118.StrictAnchorLocalization
