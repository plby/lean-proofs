import ErdosProblems.Erdos118.StrictSecondOpening
import ErdosProblems.Erdos118.CriticalLastRefinement

/-! Recover the same last/nonlast class at both actual source
checkpoints, with their separate source graphs and future-root bounds. -/

namespace Erdos118.StrictOpeningShape

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open LastBodyRefinement

theorem old_test {H : Set ℕ} {B : SimpleGraph G} (O : StrictInitialOpening.Opening H B)
    (value : Bool) (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      CriticalPair.last T.stem (lastLabel S).length = value) :
    O.opening.checkpoint.right.leaves = [] ↔ value = true :=
  O.opening.lastIff.trans (CriticalLastRefinement.initial_opening O value hall)

theorem inserted_test {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value} (W : StrictSecondOpening.Opening J)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      CriticalPair.last T.stem (lastLabel S).length = value) :
    W.opening.checkpoint.right.leaves = [] ↔ value = true := by
  have hcolor : ∀ S T : Completed, GraphPayoff.payoff W.prepared.graph .inside S T = true →
      CriticalPair.last T.stem (lastLabel S).length = value := fun S T hp ↦ hall S T
    (LastMarkerRefinement.payoff_true_mono
      (W.prepared.subgraph.trans J.inserted.subgraph) .inside S T hp)
  exact CriticalLastRefinement.at_critical W.prepared.infinite W.prepared.graph value hcolor
    W.opening.checkpoint.left W.opening.checkpoint.right W.opening.checkpoint.leftExact
    W.opening.checkpoint.rightExact W.opening.checkpoint.criticalLeft
    W.opening.checkpoint.order W.opening.checkpoint.blue

theorem inserted_rank {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value} (W : StrictSecondOpening.Opening J)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      CriticalPair.last T.stem (lastLabel S).length = value) :
    W.prepared.leafRank = W.prepared.size + 1 ↔ value = true :=
  W.opening.lastIff.symm.trans (inserted_test W hall)

theorem same_test {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value} (W : StrictSecondOpening.Opening J)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      CriticalPair.last T.stem (lastLabel S).length = value) :
    O.opening.checkpoint.right.leaves = [] ↔ W.opening.checkpoint.right.leaves = [] :=
  (old_test O value hall).trans (inserted_test W hall).symm

theorem last_future_roots {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {J : StrictTwoRootRequests.Requests O true} (W : StrictSecondOpening.Opening J)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      CriticalPair.last T.stem (lastLabel S).length = true) :
    2 ≤ O.opening.checkpoint.right.roots.length ∧ 2 ≤ W.opening.checkpoint.right.roots.length :=
  ⟨O.opening.checkpoint.twoRoots ((old_test O true hall).mpr rfl),
    W.opening.checkpoint.twoRoots ((inserted_test W hall).mpr rfl)⟩

end Erdos118.StrictOpeningShape
