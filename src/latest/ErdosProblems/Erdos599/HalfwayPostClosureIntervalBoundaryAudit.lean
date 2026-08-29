/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureIntervalTransaction
import ErdosProblems.Erdos599.HalfwayPostClosureOutsideBoundary

/-!
# Boundary audit for the actual post-closure interval row

The row selected after the moving Claim 9.31 closure is an interval linkage
from the current club frontier to the captured later frontier.  Hence its
literal outside holes can cover the initials of a reference only when those
outside initials lie on the current frontier.  This rules out using the full
global limiting reference, or the full selected-prefix reference, merely by
applying a finite proxy: a proxy changes finite character, not the initial
boundary.

A finite interval/suffix reference is valid when its members omitted from
the actual interval row have their whole carrier in the closed set.  The
second theorem is the exact symmetric-difference interface for that choice.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y Yref : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- For the actual post-closure interval, source inclusion for an outside
reference forces every surviving reference initial onto the current
frontier. -/
theorem PostClosureIntervalTransaction.outsideReference_initialSet_subset_currentSlice_of_holes
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V} {z : V}
    {R : DynamicMoving931GlobalClosure C globalZ X0}
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet)
    (hinitial : Gamma.initialSet (outsideReference Yref R.closedSet) ⊆
      Gamma.initialSet F.outside.holes.paths) :
    Gamma.initialSet (outsideReference Yref R.closedSet) ⊆
      C.newSlice := by
  have hrow := F.outsideReference_initialSet_subset_original_of_holes
    T.interval.ambientInterval_linkage.isWarp hinitial
  rw [T.interval.ambientInterval_linkage.initialSet_eq] at hrow
  simpa only [DynamicMoving931GlobalClosure.capturedGeometry_oldSlice]
    using hrow

/-- One surviving reference initial off the current frontier is therefore a
formal obstruction to the required source inclusion. -/
theorem PostClosureIntervalTransaction.not_outsideReference_initialSet_subset_holes_of_not_currentSlice
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V} {z x : V}
    {R : DynamicMoving931GlobalClosure C globalZ X0}
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet)
    (hx : x ∈ Gamma.initialSet (outsideReference Yref R.closedSet))
    (hxNotSlice : x ∉ C.newSlice) :
    ¬ Gamma.initialSet (outsideReference Yref R.closedSet) ⊆
      Gamma.initialSet F.outside.holes.paths := by
  intro hinitial
  exact hxNotSlice
    (T.outsideReference_initialSet_subset_currentSlice_of_holes
      F hinitial hx)

/-- The positive boundary package for the actual post-closure interval.
The missing-carrier premise is precisely what a finite interval
symmetric-difference closure must establish. -/
theorem PostClosureIntervalTransaction.boundaryData_of_intervalReference_sdiff_subset
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V} {z : V}
    {R : DynamicMoving931GlobalClosure C globalZ X0}
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet)
    (hmissing : Gamma.vertexSet
      (Yref \ T.interval.ambientInterval) ⊆ R.closedSet) :
    BoundaryAligned F.outside.holes.paths
        (outsideReference Yref R.closedSet) ∧
      Gamma.initialSet (outsideReference Yref R.closedSet) ⊆
        Gamma.initialSet F.outside.holes.paths :=
  F.boundaryData_of_sdiff_vertexSet_subset
    T.interval.ambientInterval_linkage.isWarp hmissing

#print axioms
  PostClosureIntervalTransaction.outsideReference_initialSet_subset_currentSlice_of_holes
#print axioms
  PostClosureIntervalTransaction.not_outsideReference_initialSet_subset_holes_of_not_currentSlice
#print axioms
  PostClosureIntervalTransaction.boundaryData_of_intervalReference_sdiff_subset

end Erdos599.Blueprint.LinkageBlueprint
