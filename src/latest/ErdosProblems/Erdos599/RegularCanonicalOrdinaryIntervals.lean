/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderSliceGeometry
import ErdosProblems.Erdos599.RegularSliceSurvivors

/-!
# Canonical ordinary intervals of a legal ladder

This module restores the small public API used by the stage-web retyping
bridge.  Its exceptional sources are exactly the nonsurviving sources, and
the ordinary realization is the survivor realization already constructed in
`RegularSliceSurvivors`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceCandidate

universe u

variable {V : Type u}

/-- Earlier-frontier sources with no essential later-stage extension. -/
def inessentialExtensionSources
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (_hL : L.SliceGeometry)
    {delta beta : Ladder.Stage kappa} (_hdeltaBeta : delta ≤ beta) : Set V :=
  RegularSliceSurvivors.nonsurvivorSources Gamma L delta beta

private theorem ordinarySources_subset_survivors
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.SliceGeometry)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta) :
    L.frontier delta \ inessentialExtensionSources hL hdeltaBeta ⊆
      RegularSliceSurvivors.survivorSources Gamma L delta beta := by
  rintro x ⟨hxFrontier, hxNotBad⟩
  by_contra hxNotSurvivor
  exact hxNotBad ⟨hxFrontier, hxNotSurvivor⟩

/-- The canonical survivor intervals between two legal ladder stages. -/
noncomputable def ordinaryStageIntervalRealization
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.SliceGeometry)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta) :
    StageIntervalRealization L delta beta
      (L.frontier delta \ inessentialExtensionSources hL hdeltaBeta) :=
  RegularSliceSurvivors.stageIntervalRealizationOfSubset_of_geometry
    (ordinarySources_subset_survivors hL hdeltaBeta) hL.roofsSourceAtStages hL.warpStages
    (hL.grows hdeltaBeta)

/-- The canonical interval meets the later frontier only at its finish. -/
theorem ordinaryStageIntervalRealization_segment_target_pure_ambient
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.SliceGeometry)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta)
    (x : ↑(L.frontier delta \
      inessentialExtensionSources hL hdeltaBeta)) :
    ((ordinaryStageIntervalRealization hL hdeltaBeta).toSegmentRealization.segment
        x).support ∩ L.frontier beta =
      {((ordinaryStageIntervalRealization hL hdeltaBeta).toSegmentRealization.segment
        x).finish} := by
  let E := RegularSliceSurvivors.essentialStageExtensionsOfSubset
    (ordinarySources_subset_survivors hL hdeltaBeta)
  change (E.segment x).support ∩ L.frontier beta = {(E.segment x).finish}
  exact RegularSliceSurvivors.segment_frontier_beta_of_geometry E
    hL.roofsSourceAtStages hL.warpStages x

/-- At a non-obstruction stage fewer than `kappa` earlier-frontier sources
fail to survive. -/
theorem mk_inessentialExtensionSources_lt_of_not_mem_phi
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.SliceGeometry)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta)
    (hbeta : beta ∉ L.phi) :
    #(inessentialExtensionSources hL hdeltaBeta) < kappa := by
  exact (RegularSliceSurvivors.mk_nonsurvivorSources_le_inessential
    hL.roofsSourceAtStages hL.warpStages
      (hL.grows hdeltaBeta)).trans_lt
        (hL.mk_inessentialWarpAt_lt_of_not_mem_phi hbeta)

end SliceCandidate
end CardinalInduction
end Erdos599
