/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerSmallness
import ErdosProblems.Erdos599.SliceStageIntervalBridge

/-!
# Actual slice geometry and ordinary intervals of the unroofed ladder

Every field of the marker-independent interface is supplied by the actual
construction. The existing interval compiler therefore retypes its literal
surviving segments in the earlier stage web, with exact ambient lifting.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Ladder KappaLadder
open CardinalInduction

universe u

variable {V : Type u} (G : DWeb V) (kappa : Cardinal.{u})
  (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
  (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)

include hNoEnter hregular huncountable in
theorem ladder_sliceGeometry : (ladder G kappa preferred).SliceGeometry := by
  have hg := ladder_geometry G kappa preferred hNoEnter
  exact
    { regular := hregular
      uncountable := huncountable
      initialStage := ladder_hasInitialStage G kappa preferred
      limitStages := hg.limitStages
      warpStages := hg.warpStages
      waveRungs := ladder_hasWaveRungs G kappa preferred
      roofMaximalRungs := ladder_hasRoofMaximalRungs G kappa preferred
      exactSuccessorArrows := ladder_hasExactSuccessorArrows G kappa preferred hNoEnter
      validBookkeeping := ladder_validBookkeeping G kappa preferred
      recordedPathsPersist := ladder_recordedPathsPersist G kappa preferred hNoEnter
      currentInessentialPersists := ladder_currentInessentialPersists G kappa preferred hNoEnter
      roofsSourceAtStages := hg.roofsSourceAtStages
      frontiersEssential := (ladder G kappa preferred).frontiersAreEssential_of_roofsSourceAtStages
        hg.roofsSourceAtStages
      frontierChronology := hg.frontierChronology
      strictFrontierChronology := ladder_hasStrictFrontierChronology G kappa preferred hNoEnter
      grows := fun {_ _} hab ↦ hg.grows hab }

include hNoEnter in
theorem ladder_heightRoofGeometry : SliceCandidate.HeightRoofGeometry (ladder G kappa preferred) :=
  ⟨ladder_hasWaveRungs G kappa preferred, ladder_hasRoofMaximalRungs G kappa preferred,
    ladder_hasExactSuccessorArrows G kappa preferred hNoEnter,
    (ladder_geometry G kappa preferred hNoEnter).roofsSourceAtStages,
    (ladder_geometry G kappa preferred hNoEnter).frontierChronology⟩

include hNoEnter hregular huncountable in
theorem mk_nonsurvivorSources_lt (hG : G.IsUnhindered) {a b : Stage kappa} (hab : a ≤ b) :
    #(RegularSliceSurvivors.nonsurvivorSources G (ladder G kappa preferred) a b) < kappa := by
  have hg := ladder_geometry G kappa preferred hNoEnter
  exact (RegularSliceSurvivors.mk_nonsurvivorSources_le_inessential
    hg.roofsSourceAtStages hg.warpStages (hg.grows hab)).trans_lt
      (mk_inessentialWarpAt_lt G kappa preferred hNoEnter hregular huncountable hG b)

include hNoEnter hregular huncountable in
/-- The actual ordinary stage linkage omits fewer than the induction cardinal
sources, has terminal-pure finite paths, and consists of literal ladder fragments. -/
theorem exists_ordinaryStageLinkage (hG : G.IsUnhindered) {a b : Stage kappa} (hab : a ≤ b) :
    let L := ladder G kappa preferred
    ∃ E : Set V, ∃ F : Set (L.stageWeb a).DPath,
      #E < kappa ∧ IsLinkageBetween (L.stageWeb a) (L.frontier a \ E) (L.frontier b) F ∧
      SliceSpliceSource.MeetsOnlyAtTerminal (L.stageWeb a) F (L.frontier b) ∧
      ∀ p ∈ F, ControlledSlices.IsLadderFragment G (L.warpAt b) (L.liftStagePath a p) := by
  dsimp only
  let L := ladder G kappa preferred
  have hL := ladder_sliceGeometry G kappa preferred hNoEnter hregular huncountable
  let E := SliceCandidate.inessentialExtensionSources hL hab
  let F := SliceCandidate.ordinaryStageFamily hL hab
  refine ⟨E, F, mk_nonsurvivorSources_lt G kappa preferred hNoEnter
    hregular huncountable hG hab,
    SliceCandidate.ordinaryStageFamily_isLinkageBetween hL hab,
    SliceCandidate.ordinaryStageFamily_meetsOnlyAtTerminal hL hab, ?_⟩
  intro p hp
  have hlift : L.liftStagePath a p ∈ SliceSegmentCore.liftStageFamily L a F := ⟨p, hp, rfl⟩
  rw [SliceCandidate.liftStageFamily_ordinaryStageFamily hL hab] at hlift
  exact SliceSegmentCore.segmentFamily_isLadderFragment
    (SliceCandidate.ordinaryStageIntervalRealization hL hab).toSegmentRealization _ hlift

#print axioms ladder_sliceGeometry
#print axioms ladder_heightRoofGeometry
#print axioms mk_nonsurvivorSources_lt
#print axioms exists_ordinaryStageLinkage

end Erdos599.DWeb.UnroofedMarker
