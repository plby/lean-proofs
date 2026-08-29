/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointContainedMovingClosure
import ErdosProblems.Erdos599.HalfwayCausalEndpointFrontier
import ErdosProblems.Erdos599.HalfwayMovingReferenceReservoir

/-!
# Contained moving closure in the actual causal Section 9 carrier

Both the reference difference and the inessential accumulated components
at club stages lie in the recorded/marker reservoir. Actual causal rows
already contain that reservoir, discharging the moving-containment premise.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint

open Set Cardinal Order DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem ClubStageGeometry.inessentialCarrierAt_subset_movingReferenceReservoir
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {b : Stage (succ kappa)} (hb : b ∈ C.club) :
    C.inessentialCarrierAt b ⊆ C.movingReferenceReservoir := by
  rintro x ⟨p, hp, hxp⟩
  have hpLimit := C.legal.mem_limitWarp_of_mem_inessential hp
  have hroof := DWeb.KappaLadder.Deferred.inessentialPath_support_subset_strictRoof_frontier
    C.ladder C.legal hp p.initial_mem_support
  have hmiss := C.inessentialPath_not_mem_limitReferenceAtFrontier b hp
  exact ⟨p, C.roofedLimitReferenceMiss_mem_recorded_or_marker hb ⟨hpLimit, hroof.1, hmiss⟩, hxp⟩

namespace CausalSection9Rows

theorem movingInessentialCarrier_subset_globalCarrier
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    {b : Stage (succ kappa)} (hb : b ∈ C.club) (hab : C.newStage < b) :
    C.movingInessentialCarrier C.newStage b ⊆
      globalCarrier Gamma kappa hkappa hGamma seed hseed := by
  have hreservoir : C.movingReferenceReservoir ⊆
      globalCarrier Gamma kappa hkappa hGamma seed hseed := by
    apply C.movingReferenceReservoir_subset_of_recorded_marker_closed
    · intro a p hp
      apply chosen_support_subset_globalCarrier hkappa hGamma hseed
      simpa only [hC] using hp
    · simpa only [hC] using
        (markerSet_subset_globalCarrier (Gamma := Gamma) hkappa hGamma hseed)
    · exact (endpoint_closedCarrier hkappa hGamma hseed C hC).reference_closed
  exact Set.union_subset
    ((C.movingReferenceDifference_subset_movingReferenceReservoir
      hab.le C.new_mem_club hb).trans hreservoir)
    ((C.inessentialCarrierAt_subset_movingReferenceReservoir hb).trans hreservoir)

/-- The same actual endpoint moving limit retains its causal carrier bound. -/
theorem exists_endpointLimitClosure_within_globalCarrier
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    {X0 : Set V} (lower : Stage (succ kappa))
    (hXcard : #X0 ≤ kappa)
    (hXZ : X0 ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed) :
    ∃ U : ColouredSafeEndpointMovingStages.LimitClosure C X0,
      U.closedSet ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed ∧
        lower < U.later.stage := by
  apply ColouredSafeEndpointMovingStages.LimitClosure.exists_of_seed_above_within
    (endpoint_closedCarrier hkappa hGamma hseed C hC)
  · simpa only [hC] using
      (globalCarrier_subset_limitRoof (Gamma := Gamma) hkappa hGamma hseed)
  · intro b hb hab
    exact movingInessentialCarrier_subset_globalCarrier hkappa hGamma hseed C hC hb hab
  · exact hXcard
  · exact hXZ

end CausalSection9Rows

#print axioms ClubStageGeometry.inessentialCarrierAt_subset_movingReferenceReservoir
#print axioms CausalSection9Rows.movingInessentialCarrier_subset_globalCarrier
#print axioms CausalSection9Rows.exists_endpointLimitClosure_within_globalCarrier

end Erdos599.Blueprint.LinkageBlueprint
