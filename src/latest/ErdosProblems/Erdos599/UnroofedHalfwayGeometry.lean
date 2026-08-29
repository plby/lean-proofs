/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedDeferredBookkeeping
import ErdosProblems.Erdos599.DeferredHalfwayGeometry
import ErdosProblems.Erdos599.UnroofedMarkerSpliceGeometry

/-!
# Actual unroofed geometry and the deferred avoiding club

The half-way geometric contract is supplied by the constructed ladder.
Equality of its ordinary and deferred bookkeeping transports the already
proved grounding and unhindered-stage club. No historical exhaustion rule
or extra deferred-grounding premise is imposed.
-/

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Ladder KappaLadder

universe u

variable {V : Type u} (G : DWeb V) (kappa : Cardinal.{u})
  (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)

include hNoEnter in
theorem ladder_markerOutsideRoof {a : Stage kappa} {y : V}
    (hy : (ladder G kappa preferred).marker a = some y) :
    y ∉ G.roof ((ladder G kappa preferred).frontier a) := by
  let L := ladder G kappa preferred
  let pref := extendLadderPreference kappa preferred
  have hg := ladder_geometry G kappa preferred hNoEnter
  have hinv := state_invariant G pref hNoEnter a.1
  intro hyRoof
  have hyOld : y ∈ G.roof (G.terminalFrontier (L.warpAt a)) := by
    rw [L.frontier_eq_essential_terminalFrontier hg.roofsSourceAtStages a,
      G.roof_essential] at hyRoof
    exact hyRoof
  exact markerAt_not_mem_preMarkerRoof G pref hy
    (G.roof_terminalFrontier_subset_canonicalArrow hNoEnter
      (state G pref a.1) hinv.warp hinv.selfRoof hinv.sourceRoof hyOld)

include hNoEnter in
theorem ladder_markerOutsideCurrentWarp {a : Stage kappa} {y : V}
    (hy : (ladder G kappa preferred).marker a = some y) :
    y ∉ G.vertexSet ((ladder G kappa preferred).warpAt a) := by
  let L := ladder G kappa preferred
  have hg := ladder_geometry G kappa preferred hNoEnter
  intro hyWarp
  apply ladder_markerOutsideRoof G kappa preferred hNoEnter hy
  rw [L.frontier_eq_essential_terminalFrontier hg.roofsSourceAtStages a, G.roof_essential]
  exact hg.selfRoofing (Stage.toExtended a) hyWarp

include hNoEnter in
theorem ladder_halfwayGeometry (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa) :
    Deferred.HalfwayGeometry (ladder G kappa preferred) := by
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
      markerOutsideRoof := fun _ _ hy ↦ ladder_markerOutsideRoof G kappa preferred hNoEnter hy
      markerInserted := fun _ _ hy ↦
        markerAt_trivial_mem_successor G (extendLadderPreference kappa preferred) hy
      markersInjective := ladder_markersInjective G kappa preferred hNoEnter
      accumulatedInitialProvenance :=
        ladder_hasAccumulatedInitialProvenance G kappa preferred hNoEnter
      validBookkeeping := ladder_deferred_validBookkeeping G kappa preferred hNoEnter
      hangingProvenance := ladder_hasHangingProvenance G kappa preferred hNoEnter
      recordedPathsPersist := ladder_recordedPathsPersist G kappa preferred hNoEnter
      currentInessentialPersists := ladder_currentInessentialPersists G kappa preferred hNoEnter
      roofsSourceAtStages := hg.roofsSourceAtStages
      frontiersEssential := (ladder G kappa preferred).frontiersAreEssential_of_roofsSourceAtStages
        hg.roofsSourceAtStages
      frontierChronology := hg.frontierChronology
      strictFrontierChronology := ladder_hasStrictFrontierChronology G kappa preferred hNoEnter }

include hNoEnter in
theorem ladder_deferred_phiHindrance_subset_phi (hNorm : G.IsNormalized) :
    (ladder G kappa preferred).phiHindrance ⊆ Deferred.phi (ladder G kappa preferred) := by
  rw [ladder_deferred_phi_eq G kappa preferred hNoEnter]
  exact phiHindrance_subset_phi_of_lemma76Data hNorm
    (ladder_lemma76Data G kappa preferred hNoEnter)

include hNoEnter in
theorem ladder_deferred_phi_not_stationary
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa) (hG : G.IsUnhindered) :
    ¬ Stationary.IsStationaryBelow kappa (Deferred.phi (ladder G kappa preferred)) := by
  rw [ladder_deferred_phi_eq G kappa preferred hNoEnter]
  exact ladder_phi_not_stationary G kappa preferred hNoEnter hregular huncountable hG

include hNoEnter in
theorem exists_deferred_club_unhindered_stages
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (hG : G.IsUnhindered) :
    ∃ C : Set (Stage kappa), Stationary.IsClubBelow kappa C ∧
      Disjoint C (Deferred.phi (ladder G kappa preferred)) ∧
      ∀ a ∈ C, ((ladder G kappa preferred).stageWeb a).IsUnhindered := by
  rw [ladder_deferred_phi_eq G kappa preferred hNoEnter]
  exact exists_club_unhindered_stages G kappa preferred hNoEnter hregular huncountable hNorm hG

#print axioms ladder_markerOutsideRoof
#print axioms ladder_markerOutsideCurrentWarp
#print axioms ladder_halfwayGeometry
#print axioms ladder_deferred_phiHindrance_subset_phi
#print axioms ladder_deferred_phi_not_stationary
#print axioms exists_deferred_club_unhindered_stages

end Erdos599.DWeb.UnroofedMarker
