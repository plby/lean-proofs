/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosurePureBoundary
import ErdosProblems.Erdos599.HalfwayPostClosureCompressorAssignment
import ErdosProblems.Erdos599.FracturedAssignmentMacroCompressorProvenance

/-!
# Actual post-closure assignment with occurrence ownership retained

This is the occurrence-aware sibling of `PostClosureCompressorAssignment`.
It uses the same literal fractured outside family and the same compressor
compiler, but retains the macro-owned selected assignment upstairs.  The
ordinary post-closure assignment is a projection of this record.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

structure PostClosureMacroCompressorAssignment
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V} {z : V}
    {R : DynamicMoving931GlobalClosure C globalZ X0}
    (T : PostClosureIntervalTransaction C globalZ X0 z R) where
  fractured : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
    (Gamma := Gamma) T.interval.ambientInterval R.closedSet
  assignment : FracturedAssignmentPeel.MacroCompressorProducedBracketFracturedAssignment
    fractured.outside.holes (outsideReference T.intervalReference R.closedSet)

namespace PostClosureMacroCompressorAssignment

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ X0 : Set V} {z : V}
variable {R : DynamicMoving931GlobalClosure C globalZ X0}
variable {T : PostClosureIntervalTransaction C globalZ X0 z R}

/-- Forget only the selected occurrence assignment.  The final compressed
assignment remains definitionally the one compiled from it. -/
def toPostClosureCompressorAssignment
    (A : PostClosureMacroCompressorAssignment T) :
    PostClosureCompressorAssignment T where
  fractured := A.fractured
  assignment := A.assignment.compiled.traversal
  compressor := A.assignment.compiled.compressor

@[simp] theorem toPostClosureCompressorAssignment_assigned
    (A : PostClosureMacroCompressorAssignment T) (s) :
    A.toPostClosureCompressorAssignment.assignment.produced.bracket.assignment.assigned s =
      A.assignment.compiled.traversal.produced.bracket.assignment.assigned s :=
  rfl

end PostClosureMacroCompressorAssignment

namespace PostClosureIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ X0 : Set V} {z : V}
variable {R : DynamicMoving931GlobalClosure C globalZ X0}

/-- The actual interval transaction admits the macro-preserving compressor
assignment.  Unlike the arbitrary-reference proxy compiler, the local
outside interval reference is genuinely finite character, so the concrete
macro assignment can be retained without changing references. -/
theorem exists_macroCompressorAssignment
    (T : PostClosureIntervalTransaction C globalZ X0 z R) :
    Nonempty (PostClosureMacroCompressorAssignment T) := by
  obtain ⟨F⟩ := exists_splitProjectedOutsideFracturedWarp
    T.interval.ambientInterval R.closedSet
    T.interval.ambientInterval_linkage.isWarp
    T.interval.ambientInterval_linkage.finiteCharacter
  obtain ⟨hboundary, hinitial⟩ := T.boundaryData_of_interval_purity F
  have hOutsideWarp : Gamma.IsWarp
      (outsideReference T.intervalReference R.closedSet) :=
    T.intervalReference_isLinkageBetween.isWarp.subset
      (outsideReference_subset (Y := T.intervalReference) (X := R.closedSet))
  have hOutsideFinite : Gamma.HasFiniteCharacter
      (outsideReference T.intervalReference R.closedSet) :=
    outsideReference_finiteCharacter
      T.intervalReference_isLinkageBetween.finiteCharacter
  obtain ⟨A⟩ :=
    FracturedAssignmentPeel.exists_macroCompressorProducedBracketFracturedAssignment
      F.outside.holes hboundary hOutsideWarp F.outside.finiteCharacter
      F.outside.edgeWarpFiniteCharacter hOutsideFinite hinitial
  exact ⟨{ fractured := F, assignment := A }⟩

end PostClosureIntervalTransaction

end Erdos599.Blueprint.LinkageBlueprint

#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureIntervalTransaction.exists_macroCompressorAssignment
