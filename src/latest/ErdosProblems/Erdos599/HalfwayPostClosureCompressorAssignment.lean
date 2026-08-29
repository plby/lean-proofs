/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureAssignedDirections
import ErdosProblems.Erdos599.FracturedAssignmentProducedCompressor

/-!
# Actual post-closure assignments retaining chronological compressor inputs

The run-walk output alone forgets the order of interior coordinates within
each run.  This additive actual-row certificate retains the compressor
input which proves that order.  The previously proved global internal
safety, backward provenance, and endpoint directions remain available on
its literal underlying produced assignment.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

structure PostClosureCompressorAssignment
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V} {z : V}
    {R : DynamicMoving931GlobalClosure C globalZ X0}
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    extends PostClosureProducedAssignment T where
  compressor : ∀ s,
    FracturedAssignmentPeel.HasCompressorRealization
      (assignment.produced.bracket.assignment.assigned s)

namespace PostClosureIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ X0 : Set V} {z : V}
variable {R : DynamicMoving931GlobalClosure C globalZ X0}

/-- The literal interval row supplies a chronological compressor witness
for every assigned path.  No numerical run-order premise is added. -/
theorem exists_compressorAssignment
    (T : PostClosureIntervalTransaction C globalZ X0 z R) :
    Nonempty (PostClosureCompressorAssignment T) := by
  obtain ⟨F⟩ := exists_splitProjectedOutsideFracturedWarp
    T.interval.ambientInterval R.closedSet
    T.interval.ambientInterval_linkage.isWarp
    T.interval.ambientInterval_linkage.finiteCharacter
  obtain ⟨hboundary, hinitial⟩ := T.boundaryData_of_interval_purity F
  have hOutsideWarp : Gamma.IsWarp
      (outsideReference T.intervalReference R.closedSet) :=
    T.intervalReference_isLinkageBetween.isWarp.subset
      (outsideReference_subset (Y := T.intervalReference) (X := R.closedSet))
  obtain ⟨A⟩ := FracturedAssignmentPeel.OutsideFracturedWarp.exists_compressorProducedBracketFracturedAssignment_anyReference
    F.outside hboundary hOutsideWarp hinitial
  exact ⟨{
    fractured := F
    assignment := A.traversal
    compressor := A.compressor
  }⟩

end PostClosureIntervalTransaction

#print axioms PostClosureIntervalTransaction.exists_compressorAssignment

end Erdos599.Blueprint.LinkageBlueprint
