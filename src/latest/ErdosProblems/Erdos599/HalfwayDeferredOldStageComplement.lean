/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayDeferredStageIntervalBridge
import ErdosProblems.Erdos599.HalfwayStageGeometryCore

/-!
# The deferred old-stage complement

For the canonical deferred ladder, the old frontier itself need not be
small.  The correct exceptional set consists of those old-frontier sources
whose essential component does not survive to the selected new stage.  It
has size at most the blueprint cardinal, while its complement carries the
literal survivor intervals retyped in the old essential quotient web.

This is the deferred-bookkeeping counterpart of the obsolete split-ladder
`HalfwayOldStageComplement` API.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open CardinalInduction
open CardinalInduction.DeferredStageInterval
open CardinalInduction.SliceCandidate

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClubStageGeometry

variable (C : ClubStageGeometry Gamma Y kappa (succ kappa))

/-- The genuine deferred exceptional set: old-frontier components with no
essential extension at the selected new stage. -/
def deferredOldStageExceptional : Set V :=
  CardinalInduction.RegularSliceSurvivors.nonsurvivorSources
    Gamma C.ladder C.oldStage C.newStage

/-- The selected new club stage avoids the deferred obstruction set. -/
theorem newStage_not_mem_deferred_phi :
    C.newStage ∉ DWeb.KappaLadder.Deferred.phi C.ladder := by
  intro hphi
  exact Set.disjoint_left.1 C.club_avoids_phi C.new_mem_club hphi

/-- Only `kappa` many old-frontier sources fail to survive. -/
theorem mk_deferredOldStageExceptional_le :
    #C.deferredOldStageExceptional ≤ kappa := by
  have hgrows : Gamma.LadderGrows
      (C.ladder.warpAt C.oldStage) (C.ladder.warpAt C.newStage) :=
    DeferredStageInterval.warpAt_grows_of_le C.legal C.old_lt_new.le
  have hle : #C.deferredOldStageExceptional ≤
      #(Gamma.inessentialPaths (C.ladder.warpAt C.newStage)) :=
    CardinalInduction.RegularSliceSurvivors.mk_nonsurvivorSources_le_inessential
      C.legal.roofsSourceAtStages C.legal.warpStages hgrows
  have hlt : #(Gamma.inessentialPaths (C.ladder.warpAt C.newStage)) <
      succ kappa :=
    DWeb.KappaLadder.Deferred.mk_inessentialWarpAt_lt_of_not_mem_phi
      C.legal C.newStage C.newStage_not_mem_deferred_phi
  exact (lt_succ_iff.mp (hle.trans_lt hlt))

/-- The survivors are precisely the complement of the exceptional set in
the old frontier. -/
theorem oldSlice_diff_deferredExceptional_subset_survivors :
    C.oldSlice \ C.deferredOldStageExceptional ⊆
      CardinalInduction.RegularSliceSurvivors.survivorSources
        Gamma C.ladder C.oldStage C.newStage := by
  rintro x ⟨hxOld, hxNotExceptional⟩
  by_contra hxNotSurvivor
  exact hxNotExceptional ⟨hxOld, hxNotSurvivor⟩

/-- The canonical deferred survivor realization between the two selected
club stages. -/
noncomputable def deferredOldStageRealization :
    StageIntervalRealization C.ladder C.oldStage C.newStage
      (C.oldSlice \ C.deferredOldStageExceptional) :=
  CardinalInduction.RegularSliceSurvivors.stageIntervalRealizationOfSubset_of_geometry
    C.oldSlice_diff_deferredExceptional_subset_survivors
    C.legal.roofsSourceAtStages C.legal.warpStages
    (DeferredStageInterval.warpAt_grows_of_le C.legal C.old_lt_new.le)

/-- The literal ordinary survivor intervals, typed in the old essential
quotient stage. -/
noncomputable def deferredOldStageOrdinaryFamily :
    Set (C.ladder.stageWeb C.oldStage).DPath :=
  DeferredStageInterval.StageIntervalRealization.stageFamily
    C.deferredOldStageRealization C.legal C.old_lt_new.le

theorem deferredOldStageOrdinaryFamily_isLinkageBetween :
    IsLinkageBetween (C.ladder.stageWeb C.oldStage)
      (C.oldSlice \ C.deferredOldStageExceptional) C.newSlice
      C.deferredOldStageOrdinaryFamily := by
  exact DeferredStageInterval.StageIntervalRealization.stageFamily_isLinkageBetween
    C.deferredOldStageRealization C.legal C.old_lt_new.le

theorem deferredOldStageOrdinaryFamily_meetsOnlyAtTerminal :
    SliceSpliceSource.MeetsOnlyAtTerminal
      (C.ladder.stageWeb C.oldStage)
      C.deferredOldStageOrdinaryFamily C.newSlice := by
  exact DeferredStageInterval.StageIntervalRealization.stageFamily_meetsOnlyAtTerminal
    C.deferredOldStageRealization C.legal C.old_lt_new.le

/-- Ambient lifting recovers the exact family of literal survivor
intervals. -/
@[simp] theorem liftStageFamily_deferredOldStageOrdinaryFamily :
    SliceSegmentCore.liftStageFamily C.ladder C.oldStage
        C.deferredOldStageOrdinaryFamily =
      SliceSegmentCore.segmentFamily
        C.deferredOldStageRealization.toSegmentRealization := by
  exact DeferredStageInterval.StageIntervalRealization.liftStageFamily_stageFamily
    C.deferredOldStageRealization C.legal C.old_lt_new.le

#print axioms deferredOldStageRealization
#print axioms deferredOldStageOrdinaryFamily_isLinkageBetween
#print axioms mk_deferredOldStageExceptional_le
#print axioms liftStageFamily_deferredOldStageOrdinaryFamily

end ClubStageGeometry
end Erdos599.Blueprint.LinkageBlueprint
