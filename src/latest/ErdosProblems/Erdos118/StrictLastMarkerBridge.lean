import ErdosProblems.Erdos118.CrossMarkerBridge
import ErdosProblems.Erdos118.AlignedBridgeDiagram

/-! The actual first marker bridge in the strict last class. Both
paused source bounds precede the target run; its U suffix is retained. -/

namespace Erdos118.StrictLastMarkerBridge

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open BlueRuns LastBodyRefinement

structure Diagram {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {J : StrictTwoRootRequests.Requests O true} {W : StrictSecondOpening.Opening J}
    {Q : StrictSharedBodyRequests.Requests W} {F : StrictSharedFirstLeaves.Pair Q}
    (R : StrictMarkerRequests.Requests F) where
  checkpoint : StrictTargetCheckpoint.Checkpoint W (max R.old.bound R.inserted.bound)
  bridge : CrossMarkerBridge.Aligned O.prepared.alphabet W.prepared.alphabet
    O.prepared.graph J.graph F.oldLeft O.opening.checkpoint.right checkpoint.left checkpoint.right
    R.oldRest (max R.old.bound R.inserted.bound)
  sourceNonempty : bridge.source.roots ≠ []
  sourceRequest : AlignedBridgeDiagram.RightBody O.prepared.alphabet O.prepared.graph
    F.oldLeft bridge.source
  targetRequest : InsertedAlignment.PositiveBody W.prepared.alphabet J.graph
    bridge.target checkpoint.right
  rightRest : List ℕ
  rightRoots : checkpoint.right.roots = W.reserve.labels.next :: rightRest
  rightLeaves : checkpoint.right.leaves = []
  rightFresh : ∃ v : List ℕ,
    checkpoint.right.position.ordinary = W.opening.checkpoint.right.position.ordinary ++ v ∧
    ∀ x ∈ v, x ∈ W.prepared.alphabet ∧ R.inserted.bound < x
  targetRun : ConservativeRuns.Run W.prepared.alphabet (GraphPayoff.payoff J.graph .inside)
    (.leaf (StrictTwoRootRequests.target O), .leaf (StrictTargetCheckpoint.rightTarget W))
    (.body bridge.target, .leaf checkpoint.right)
  targetFresh : FreshCheckpoints.FreshExtension W.prepared.alphabet
    (max R.old.bound R.inserted.bound)
    (.leaf (StrictTwoRootRequests.target O), .leaf (StrictTargetCheckpoint.rightTarget W))
    (.body bridge.target, .leaf checkpoint.right)

theorem exists_diagram {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {J : StrictTwoRootRequests.Requests O true} {W : StrictSecondOpening.Opening J}
    {Q : StrictSharedBodyRequests.Requests W} {F : StrictSharedFirstLeaves.Pair Q}
    (R : StrictMarkerRequests.Requests F) (hanchor : W.anchorRank = J.rank + 1)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      CriticalPair.last T.stem (lastLabel S).length = true)
    (hlast : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (lastLabel S).length ≠ 1) : Nonempty (Diagram R) := by
  let d := max R.old.bound R.inserted.bound
  obtain ⟨C⟩ := StrictTargetCheckpoint.exists_checkpoint W hall d
  obtain ⟨hTR, hTL⟩ := StrictMarkerRequests.target_left_next C
  obtain ⟨⟨rest, hUR⟩, hUL⟩ := StrictMarkerRequests.target_right_next C hanchor
  have hKJ : W.prepared.alphabet ⊆ J.alphabet := W.prepared.subset.trans J.inserted.subset
  have hKH : W.prepared.alphabet ⊆ O.prepared.alphabet := hKJ.trans J.subset
  have hcommand : LeftBlue W.prepared.alphabet (GraphPayoff.payoff J.graph .inside)
      (.leaf C.left, .leaf C.right) := by
    obtain ⟨n, A, hs, hA, b, hc⟩ := C.command
    exact ⟨n, A, hs, hA, b, fun a ha hlarge ↦
      (hc a (ha.trans hKJ) hlarge).almost_mono (RamseyGame.almostSubset_of_subset hKJ)⟩
  have hroot₀ : (StrictTwoRootRequests.target O).position.stem.root =
      O.opening.checkpoint.right.position.stem.root := by
    change O.opening.target.position.stem.root = _
    have he := congrArg (fun l : List ℕ ↦ l.headD 0) O.opening.ordinary
    simpa only [Position.ordinary, Stem.ordinary, List.cons_append, List.headD_cons] using he
  have hroot : C.left.position.stem.root = O.opening.checkpoint.right.position.stem.root :=
    ((List.cons_prefix_cons.mp (SkippedCuts.run_extensions C.run).1.ordinary).1.symm).trans hroot₀
  obtain ⟨u, v, hu, hv, huf, hvf⟩ := C.fresh
  have hword : C.left.position.ordinary = O.opening.checkpoint.right.position.ordinary ++ u := by
    change C.left.position.ordinary = O.opening.target.position.ordinary ++ u at hu
    rwa [O.opening.ordinary] at hu
  have hf : ∀ x ∈ u, x ∈ O.prepared.alphabet ∧ R.old.bound < x :=
    fun x hx ↦ ⟨hKH (huf x hx).1, (le_max_left _ _).trans_lt (huf x hx).2⟩
  obtain ⟨D⟩ := CrossMarkerBridge.align W.prepared.infinite hKH O.prepared.graph J.graph
    F.oldLeft O.opening.checkpoint.right C.left C.right O.reserve.labels.next R.oldRest
    R.oldRoots R.oldLeaves hTR hTL O.opening.checkpoint.rightExact C.leftExact hroot
    R.old u hword hf hcommand d
  have hDnonempty : D.source.roots ≠ [] := by
    rw [D.sourceRoots]
    exact R.oldNonempty
  obtain ⟨k, b, hb⟩ := PreparedRelays.body_setups O.prepared.graph .inside true
    D.source (.leaf F.oldLeft) D.sourceCommand
  let oldRequest : AlignedBridgeDiagram.RightBody O.prepared.alphabet O.prepared.graph
      F.oldLeft D.source := ⟨k, b, hb⟩
  obtain ⟨targetRequest⟩ := InsertedAlignment.positive_body W.prepared.infinite J.graph
    (fun S T hp ↦ hlast S T (LastMarkerRefinement.payoff_true_mono J.subgraph .inside S T hp))
    D.target C.right D.targetExact D.targetRoots D.targetCommand
  have hrightFresh : ∃ w : List ℕ,
      C.right.position.ordinary = W.opening.checkpoint.right.position.ordinary ++ w ∧
      ∀ x ∈ w, x ∈ W.prepared.alphabet ∧ R.inserted.bound < x := by
    refine ⟨v, ?_, fun x hx ↦ ⟨(hvf x hx).1, (le_max_right _ _).trans_lt (hvf x hx).2⟩⟩
    change C.right.position.ordinary = W.opening.target.position.ordinary ++ v at hv
    rwa [W.opening.ordinary] at hv
  exact ⟨{
    checkpoint := C, bridge := D, sourceNonempty := hDnonempty
    sourceRequest := oldRequest, targetRequest := targetRequest
    rightRest := rest, rightRoots := hUR, rightLeaves := hUL, rightFresh := hrightFresh
    targetRun := Relation.ReflTransGen.tail C.run D.targetStep
    targetFresh := FreshCheckpoints.fresh_trans C.fresh D.fresh }⟩

end Erdos118.StrictLastMarkerBridge
