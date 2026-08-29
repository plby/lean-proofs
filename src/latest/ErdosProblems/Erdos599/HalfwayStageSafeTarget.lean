/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayStageGeometryCore
import ErdosProblems.Erdos599.RegularSafeCompletion
import ErdosProblems.Erdos599.SliceDeltaLift

/-!
# The deletion-safe path used by the half-way successor transaction

Assertion 9.23 is applied in the old essential quotient stage, not in the
ambient web.  This file records that application without prematurely
replacing the chosen path by an unrelated ambient linkage.  The singleton
stage family remains safely deletable, and its literal stage lift is an
ambient path from the scheduled old-frontier vertex to the original target.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath
open CardinalInduction

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-- The exact output of Assertion 9.23 at a scheduled old-frontier vertex.

The stage family is retained because its safely deleted residual is the
input to the source-faithful extension step.  The ambient family is its
literal lift, so the selected target path and all of its vertices are still
available to the subsequent closure and accounting constructions. -/
structure SafeOldStageTargetPath
    (C : ClubStageGeometry Gamma Y kappa theta) (z : V) where
  stageFamily : Set (C.ladder.stageWeb C.oldStage).DPath
  stage_linkage : IsLinkageBetween (C.ladder.stageWeb C.oldStage)
    {z} (C.ladder.stageWeb C.oldStage).target stageFamily
  deletion_safe :
    ((C.ladder.stageWeb C.oldStage).delete
      ((C.ladder.stageWeb C.oldStage).vertexSet stageFamily)).IsUnhindered
  ambientFamily : Set Gamma.DPath
  ambient_eq_lift : ambientFamily =
    SliceSegmentCore.liftStageFamily C.ladder C.oldStage stageFamily
  ambient_linkage :
    IsLinkageBetween Gamma {z} Gamma.target ambientFamily

namespace SafeOldStageTargetPath

variable {C : ClubStageGeometry Gamma Y kappa theta} {z : V}

/-- Every retained stage member has its literal ambient lift in the
ambient family. -/
theorem lift_mem (P : SafeOldStageTargetPath C z)
    {p : (C.ladder.stageWeb C.oldStage).DPath}
    (hp : p ∈ P.stageFamily) :
    C.ladder.liftStagePath C.oldStage p ∈ P.ambientFamily := by
  rw [P.ambient_eq_lift]
  exact ⟨p, hp, rfl⟩

/-- The ambient carrier of the retained family is exactly the stage
carrier.  In particular no selected-path vertex is forgotten by lifting. -/
theorem ambient_vertexSet_eq (P : SafeOldStageTargetPath C z) :
    Gamma.vertexSet P.ambientFamily =
      (C.ladder.stageWeb C.oldStage).vertexSet P.stageFamily := by
  rw [P.ambient_eq_lift]
  ext x
  constructor
  · rintro ⟨_q, ⟨p, hp, rfl⟩, hxp⟩
    refine ⟨p, hp, ?_⟩
    rwa [SliceSegmentCore.liftStagePath_support] at hxp
  · rintro ⟨p, hp, hxp⟩
    refine ⟨C.ladder.liftStagePath C.oldStage p, ⟨p, hp, rfl⟩, ?_⟩
    rwa [SliceSegmentCore.liftStagePath_support]

end SafeOldStageTargetPath

/-- Source Theorem 6.1, applied in the old club stage, supplies the exact
deletion-safe singleton path required by Assertion 9.23.  Its ambient lift
is an honest singleton linkage to the original target because stage lifting
preserves supports and both endpoints. -/
theorem ClubStageGeometry.exists_safeOldStageTargetPath
    (C : ClubStageGeometry Gamma Y kappa theta)
    {z : V} (hz : z ∈ C.oldSlice) :
    Nonempty (SafeOldStageTargetPath C z) := by
  let H := C.ladder.stageWeb C.oldStage
  obtain ⟨c⟩ := CardinalInduction.RegularSafeCompletion.exists_safeCompletionChoice
    H ∅ (by simpa [H] using C.oldStage_isUnhindered) hz (by simp)
  let P : Set H.DPath := c.family
  have hP : IsLinkageBetween H {z} H.target P :=
    c.family_isLinkageBetween
  have hsafe : (H.delete (H.vertexSet P)).IsUnhindered := by
    rw [c.vertexSet_family]
    simpa only [empty_union] using c.next_unhindered
  let Q : Set Gamma.DPath :=
    SliceSegmentCore.liftStageFamily C.ladder C.oldStage P
  have hQ : IsLinkageBetween Gamma {z} Gamma.target Q := by
    exact CardinalInduction.SliceDeltaLift.IsLinkageBetween.liftStageFamily hP
  exact ⟨{
    stageFamily := P
    stage_linkage := hP
    deletion_safe := hsafe
    ambientFamily := Q
    ambient_eq_lift := rfl
    ambient_linkage := hQ }⟩

end LinkageBlueprint
end Blueprint
end Erdos599
