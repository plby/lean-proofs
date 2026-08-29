/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMovingGlobalClosure

/-!
# The club-stage geometry selected after the Assertion 9.31 closure

The small set in Claim 9.31 is completed before the later ordinal is
chosen.  Consequently the interval linkage used by Assertion 9.31 runs
from the current club stage of the original geometry to the captured club
stage, not between the original fixed pair of stages.

This file packages that change of indices.  The closed-stage family is the
constant completed set.  Thus its value at the new stage and its strict
union before that stage are both exactly the completed set, and the
required cardinal bound is the one proved by the dynamic closure.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace DynamicMoving931GlobalClosure

/-- Re-index the one-step geometry at the genuinely later club stage
selected after the dynamic global-reference closure. -/
def capturedGeometry
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V}
    (R : DynamicMoving931GlobalClosure C globalZ X0) :
    ClubStageGeometry Gamma Y kappa (succ kappa) where
  ladder := C.ladder
  legal := C.legal
  hindranceRungs := C.hindranceRungs
  hindranceObstruction := C.hindranceObstruction
  normalized := C.normalized
  club := C.club
  club_isClub := C.club_isClub
  club_avoids_phi := C.club_avoids_phi
  oldStage := C.newStage
  newStage := R.later.stage
  old_mem_club := C.new_mem_club
  new_mem_club := R.later.mem_club
  old_lt_new := R.later.current_lt
  closedStage := fun _ => R.closedSet
  closedStage_mono := by
    intro a b hab x hx
    exact hx
  before_card := by
    apply (Cardinal.mk_subtype_mono ?_).trans R.card_le
    intro x hx
    obtain ⟨a, ha, hxa⟩ := hx
    exact hxa
  capacity_infinite := C.capacity_infinite

@[simp] theorem capturedGeometry_ladder
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V}
    (R : DynamicMoving931GlobalClosure C globalZ X0) :
    R.capturedGeometry.ladder = C.ladder := rfl

@[simp] theorem capturedGeometry_oldStage
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V}
    (R : DynamicMoving931GlobalClosure C globalZ X0) :
    R.capturedGeometry.oldStage = C.newStage := rfl

@[simp] theorem capturedGeometry_newStage
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V}
    (R : DynamicMoving931GlobalClosure C globalZ X0) :
    R.capturedGeometry.newStage = R.later.stage := rfl

@[simp] theorem capturedGeometry_closedSet
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V}
    (R : DynamicMoving931GlobalClosure C globalZ X0) :
    R.capturedGeometry.closedSet = R.closedSet := rfl

/-- Because the closed family is constant, its strict union before the
captured stage is the completed Claim 9.31 set itself. -/
@[simp] theorem capturedGeometry_before
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V}
    (R : DynamicMoving931GlobalClosure C globalZ X0) :
    R.capturedGeometry.before = R.closedSet := by
  change closedBefore (fun _ => R.closedSet) R.later.stage = R.closedSet
  ext x
  constructor
  · rintro ⟨a, ha, hxa⟩
    exact hxa
  · intro hx
    exact ⟨C.newStage, R.later.current_lt, hx⟩

@[simp] theorem capturedGeometry_oldSlice
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V}
    (R : DynamicMoving931GlobalClosure C globalZ X0) :
    R.capturedGeometry.oldSlice = C.newSlice := rfl

@[simp] theorem capturedGeometry_newSlice
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V}
    (R : DynamicMoving931GlobalClosure C globalZ X0) :
    R.capturedGeometry.newSlice = C.ladder.frontier R.later.stage := rfl

theorem capturedGeometry_closedSet_subset_newRoof
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V}
    (R : DynamicMoving931GlobalClosure C globalZ X0) :
    R.capturedGeometry.closedSet ⊆ R.capturedGeometry.outerRoof := by
  change R.closedSet ⊆ Gamma.roof (C.ladder.frontier R.later.stage)
  exact R.later.subset_roof

end DynamicMoving931GlobalClosure

#print axioms DynamicMoving931GlobalClosure.capturedGeometry_before
#print axioms
  DynamicMoving931GlobalClosure.capturedGeometry_closedSet_subset_newRoof

end Erdos599.Blueprint.LinkageBlueprint
