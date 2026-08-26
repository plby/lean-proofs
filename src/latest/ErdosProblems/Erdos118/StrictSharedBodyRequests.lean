import ErdosProblems.Erdos118.StrictSecondOpening
import ErdosProblems.Erdos118.InsertedCrossAlignment

/-! The two actual shared last-body requests in the strict three-game
configuration. Both positive parameters are fixed before sampling labels. -/

namespace Erdos118.StrictSharedBodyRequests

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open BlueRuns InsideCounts LastBodyRefinement

structure Requests {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value}
    (W : StrictSecondOpening.Opening J) where
  aligned : InsertedCrossAlignment.Aligned O.prepared.alphabet W.prepared.alphabet
    O.prepared.graph W.prepared.graph O.opening.checkpoint.left W.opening.checkpoint.left
    O.opening.checkpoint.right W.opening.checkpoint.right
  old : InsertedAlignment.PositiveBody O.prepared.alphabet O.prepared.graph
    aligned.old O.opening.checkpoint.right
  inserted : InsertedAlignment.PositiveBody W.prepared.alphabet W.prepared.graph
    aligned.inserted W.opening.checkpoint.right

theorem exists_requests {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value}
    (W : StrictSecondOpening.Opening J)
    (hlast : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (lastLabel S).length ≠ 1) : Nonempty (Requests W) := by
  have hKH : W.prepared.alphabet ⊆ O.prepared.alphabet :=
    W.prepared.subset.trans (J.inserted.subset.trans J.subset)
  obtain ⟨v, hv, hvf⟩ := W.extension
  obtain ⟨_, _, hPL⟩ := O.opening.checkpoint.criticalLeft
  obtain ⟨A⟩ := InsertedCrossAlignment.align W.prepared.infinite hKH
    O.prepared.graph W.prepared.graph O.opening.checkpoint.left W.opening.checkpoint.left
    O.opening.checkpoint.right W.opening.checkpoint.right J.oldRoot J.oldRootEq hPL
    W.roots W.leaves O.opening.checkpoint.leftExact W.opening.checkpoint.leftExact
    W.root J.oldBound J.oldCertificate v hv hvf W.opening.checkpoint.command
  have hOld : O.prepared.graph ≤ B := O.prepared.subgraph.trans O.subgraph
  have hInserted : W.prepared.graph ≤ B := W.prepared.subgraph.trans J.inserted.subgraph
  obtain ⟨D⟩ := InsertedAlignment.positive_body O.prepared.infinite O.prepared.graph
    (fun S T hp ↦ hlast S T (LastMarkerRefinement.payoff_true_mono hOld .inside S T hp))
    A.old O.opening.checkpoint.right A.oldExact A.oldRoots A.oldCommand
  obtain ⟨E⟩ := InsertedAlignment.positive_body W.prepared.infinite W.prepared.graph
    (fun S T hp ↦ hlast S T (LastMarkerRefinement.payoff_true_mono hInserted .inside S T hp))
    A.inserted W.opening.checkpoint.right A.insertedExact A.insertedRoots A.insertedCommand
  exact ⟨⟨A, D, E⟩⟩

end Erdos118.StrictSharedBodyRequests
