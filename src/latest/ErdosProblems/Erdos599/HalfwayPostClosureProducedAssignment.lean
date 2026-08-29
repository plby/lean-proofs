/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayIntervalGlobalReferenceEmbedding
import ErdosProblems.Erdos599.FracturedAssignmentProducedRunWalk
import ErdosProblems.Erdos599.ArbitraryReferenceEndpointClassification
import ErdosProblems.Erdos599.ReferenceSubpathEmbeddingProvenance

/-!
# Produced post-closure assignments with global internal safeness

The finite and infinite traversal certificates are now attached to the
literal holes of the actual interval row.  Boundary purity supplies all
assignment hypotheses.  Injective interval-to-limit ownership transports
internal safeness globally, without identifying the two references or
assuming full exposed-endpoint safeness.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open _root_.Erdos599.DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The actual projected holes with all traversal and backward-owner data
retained by the compiler. -/
structure PostClosureProducedAssignment
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V} {z : V}
    {R : DynamicMoving931GlobalClosure C globalZ X0}
    (T : PostClosureIntervalTransaction C globalZ X0 z R) where
  fractured : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
    (Gamma := Gamma) T.interval.ambientInterval R.closedSet
  assignment : FracturedAssignmentPeel.TraversalProducedBracketFracturedAssignment
    fractured.outside.holes (outsideReference T.intervalReference R.closedSet)

namespace PostClosureIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ X0 : Set V} {z : V}
variable {R : DynamicMoving931GlobalClosure C globalZ X0}

/-- Actual source-order assignment production requires no extra geometric
input beyond the interval transaction already constructed. -/
theorem exists_producedAssignment
    (T : PostClosureIntervalTransaction C globalZ X0 z R) :
    Nonempty (PostClosureProducedAssignment T) := by
  obtain ⟨F⟩ := exists_splitProjectedOutsideFracturedWarp
    T.interval.ambientInterval R.closedSet
    T.interval.ambientInterval_linkage.isWarp
    T.interval.ambientInterval_linkage.finiteCharacter
  obtain ⟨hboundary, hinitial⟩ := T.boundaryData_of_interval_purity F
  have hOutsideWarp : Gamma.IsWarp
      (outsideReference T.intervalReference R.closedSet) :=
    T.intervalReference_isLinkageBetween.isWarp.subset
      (outsideReference_subset (Y := T.intervalReference) (X := R.closedSet))
  obtain ⟨A⟩ := FracturedAssignmentPeel.OutsideFracturedWarp.exists_traversalProducedBracketFracturedAssignment_anyReference
    F.outside hboundary hOutsideWarp hinitial
  exact ⟨{ fractured := F, assignment := A }⟩

end PostClosureIntervalTransaction

namespace PostClosureProducedAssignment

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ X0 : Set V} {z : V}
variable {R : DynamicMoving931GlobalClosure C globalZ X0}
variable {T : PostClosureIntervalTransaction C globalZ X0 z R}

/-- Each path actually assigned to a hole is internally safe for the global
limiting reference.  Its exposed endpoints are still classified separately. -/
theorem assigned_internallySafe_global
    (A : PostClosureProducedAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference R.closedSet)}) :
    InternallySafe C.ladder.limitWarp
      (A.assignment.produced.bracket.assignment.assigned s) := by
  apply T.internallySafe_limitWarp
  apply InternallySafe.of_safe_outsideReference
    T.intervalReference_isLinkageBetween.isWarp
  exact (A.assignment.produced.bracket.bracket_safe s).isSafe

/-- The actual backward-owner indices also promote to the global reference;
the assigned trace and its run-walk realization stay literally unchanged. -/
def assigned_backward_global
    (A : PostClosureProducedAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference R.closedSet)}) :
    FracturedAssignmentPeel.HasIndexedBackwardProvenance
      (A.assignment.produced.bracket.assignment.assigned s)
      C.ladder.limitWarp :=
  T.intervalGlobalReferenceEmbedding.hasIndexedBackwardProvenance
    ((A.assignment.produced.backward s).mono
      (outsideReference_subset (Y := T.intervalReference) (X := R.closedSet)))

end PostClosureProducedAssignment

#print axioms PostClosureIntervalTransaction.exists_producedAssignment
#print axioms PostClosureProducedAssignment.assigned_internallySafe_global
#print axioms PostClosureProducedAssignment.assigned_backward_global

end Erdos599.Blueprint.LinkageBlueprint
