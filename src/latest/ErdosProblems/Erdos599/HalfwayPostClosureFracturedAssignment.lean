/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureIntervalBoundaryAudit
import ErdosProblems.Erdos599.ArbitraryReferenceFracturedAssignment

/-!
# The literal fractured assignment for the post-closure interval row

This is the source-order composition used in Assertion 9.31.  The current-
to-later interval linkage is selected after `X`; it is then cut literally at
`X`.  The reference supplied to the fractured assignment is the untouched
outside part of the finite canonical interval reference.  The arbitrary
limiting warp is not silently identified with this finite reference; its
later globalization is a separate step.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The concrete literal holes and their bracket-preserving assignment.
No abstract simultaneous-assignment provider is stored. -/
structure PostClosureBracketFracturedAssignment
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V} {z : V}
    {R : DynamicMoving931GlobalClosure C globalZ X0}
    (T : PostClosureIntervalTransaction C globalZ X0 z R) where
  fractured : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
    (Gamma := Gamma) T.interval.ambientInterval R.closedSet
  assignment : FracturedAssignmentPeel.BracketFracturedAssignment
    fractured.outside.holes
    (outsideReference T.intervalReference R.closedSet)

namespace PostClosureIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ X0 : Set V} {z : V}
variable {R : DynamicMoving931GlobalClosure C globalZ X0}

/-- Cut the actual post-closure interval and apply the ray-compatible
fractured assignment theorem.  The two hypotheses are exactly the moving
symmetric-difference closure conclusions exposed by
`intervalReference_sdiff_vertexSet_subset`. -/
theorem exists_bracketFracturedAssignment
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    (hrootPaths : ∀ p ∈ T.intervalReference,
      p.initial ∈
          ((R.capturedGeometry.deferredOldStageExceptional ∪ {z}) ∪
            oldStageContactInitials R.capturedGeometry T.interval.safe) →
        p.support ⊆ R.closedSet)
    (hcomponents : T.interval.exceptionalComponents ⊆ R.closedSet) :
    Nonempty (PostClosureBracketFracturedAssignment T) := by
  obtain ⟨F⟩ := exists_splitProjectedOutsideFracturedWarp
    T.interval.ambientInterval R.closedSet
    T.interval.ambientInterval_linkage.isWarp
    T.interval.ambientInterval_linkage.finiteCharacter
  have hmissing : Gamma.vertexSet
      (T.intervalReference \ T.interval.ambientInterval) ⊆ R.closedSet :=
    T.intervalReference_sdiff_vertexSet_subset hrootPaths hcomponents
  obtain ⟨hboundary, hinitial⟩ :=
    T.boundaryData_of_intervalReference_sdiff_subset F hmissing
  have hOutsideWarp : Gamma.IsWarp
      (outsideReference T.intervalReference R.closedSet) :=
    T.intervalReference_isLinkageBetween.isWarp.subset
      (outsideReference_subset
        (Y := T.intervalReference) (X := R.closedSet))
  obtain ⟨A⟩ := F.outside.exists_bracketFracturedAssignment_anyReference
    hboundary hOutsideWarp hinitial
  exact ⟨{ fractured := F, assignment := A }⟩

end PostClosureIntervalTransaction

#print axioms PostClosureIntervalTransaction.exists_bracketFracturedAssignment

end Erdos599.Blueprint.LinkageBlueprint
