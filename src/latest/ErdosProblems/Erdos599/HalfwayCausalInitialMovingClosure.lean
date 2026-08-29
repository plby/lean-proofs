/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeInitialReferenceDifference
import ErdosProblems.Erdos599.ColouredSafeEndpointInitialStageSafety
import ErdosProblems.Erdos599.HalfwayCausalEndpointMovingClosure
import ErdosProblems.Erdos599.HalfwayExplicitStageResidual

/-!
# Actual contained moving closure for a safe path at stage zero

The first reference difference is small and already in the actual causal
carrier. Insert it in the seed of the existing endpoint moving closure.
The triangle inclusion then absorbs the zero-to-limit difference without
assuming that zero belongs to the avoiding club, or that a stage precedes
zero. The output is ready for the still separate initial interval splice.
-/

namespace Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows

open Set Cardinal Order DirectedPath Ladder ColouredSafeEndpointBlueprint
open _root_.Erdos599.CardinalInduction

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

theorem initial_movingReferenceDifference_subset_globalCarrier
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (hUnhindered : Gamma.IsUnhindered) {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    {b : Stage (succ kappa)} (hb : b ∈ C.club) :
    C.movingReferenceDifference (initialStage C) b ⊆
      globalCarrier Gamma kappa hkappa hGamma seed hseed := by
  apply (C.initial_movingReferenceDifference_subset_reservoir hUnhindered hb).trans
  apply C.movingReferenceReservoir_subset_of_recorded_marker_closed
  · intro a p hp
    apply chosen_support_subset_globalCarrier hkappa hGamma hseed
    simpa only [hC] using hp
  · simpa only [hC] using
      (markerSet_subset_globalCarrier (Gamma := Gamma) hkappa hGamma hseed)
  · exact (endpoint_closedCarrier hkappa hGamma hseed C hC).reference_closed

/-- The same actual closure absorbs the zero-to-limit difference after a
single explicit seed enlargement. All ordinary closure fields are retained. -/
theorem exists_initialEndpointLimitClosure_within_globalCarrier
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (hUnhindered : Gamma.IsUnhindered) {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    {X0 : Set V} (lower : Stage (succ kappa))
    (hXcard : #X0 ≤ kappa)
    (hXZ : X0 ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed) :
    ∃ U : ColouredSafeEndpointMovingStages.LimitClosure C X0,
      U.closedSet ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed ∧
      lower < U.later.stage ∧
      C.movingReferenceDifference (initialStage C) U.later.stage ⊆ U.closedSet := by
  let X1 := X0 ∪ C.movingReferenceDifference (initialStage C) C.newStage
  have hX1card : #X1 ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hkappa hXcard
      (C.mk_initial_movingReferenceDifference_le hUnhindered C.new_mem_club))
  have hX1Z : X1 ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed :=
    Set.union_subset hXZ (initial_movingReferenceDifference_subset_globalCarrier
      hkappa hGamma hUnhindered hseed C hC C.new_mem_club)
  obtain ⟨R, hRZ, hRlower⟩ := exists_endpointLimitClosure_within_globalCarrier
    hkappa hGamma hseed C hC lower hX1card hX1Z
  refine ⟨{ R with seed_subset := Set.subset_union_left.trans R.seed_subset },
    hRZ, hRlower, ?_⟩
  exact (C.movingReferenceDifference_triangle (initialStage C) C.newStage R.later.stage).trans
    (Set.union_subset (Set.subset_union_right.trans R.seed_subset) R.difference_subset)

/-- Retrieve the actual zero-stage safe path and close it together with the
designated source set before making any interval-linkage choice. -/
theorem exists_safeInitialPath_and_containedClosure
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (hUnhindered : Gamma.IsUnhindered) {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    {A0 : Set V} (hA0source : A0 ⊆ Gamma.source) (hA0card : #A0 ≤ kappa)
    (hA0Z : A0 ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    {z : V} (hz : z ∈ A0) :
    ∃ (P : SafeStageTargetPath C (initialStage C) z)
      (U : ColouredSafeEndpointMovingStages.LimitClosure C
        (A0 ∪ Gamma.vertexSet P.ambientFamily)),
      U.closedSet ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed ∧
      C.movingReferenceDifference (initialStage C) U.later.stage ⊆ U.closedSet := by
  obtain ⟨P, hPZ, hPcard⟩ := exists_safeInitialStageTargetPath_in_globalCarrier
    hkappa hGamma hUnhindered hseed C hC ⟨hA0source hz, hA0Z hz⟩
  have hcard : #(↑(A0 ∪ Gamma.vertexSet P.ambientFamily)) ≤ kappa :=
    (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hkappa hA0card hPcard)
  obtain ⟨U, hUZ, _hlower, hdiff⟩ := exists_initialEndpointLimitClosure_within_globalCarrier
    hkappa hGamma hUnhindered hseed C hC C.newStage hcard (Set.union_subset hA0Z hPZ)
  exact ⟨P, U, hUZ, hdiff⟩

/-- The actual initial safe choice and contained closure supply a linkable
deleted interval at the very same later frontier. The current extension
premise is genuine; no first-club blueprint or completed row is assumed. -/
theorem exists_safeInitialPath_closedResidual
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (hUnhindered : Gamma.IsUnhindered) {seed : Set V} (hseed : #seed ≤ succ kappa)
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (hC : C.ladder = finalLadder Gamma kappa hkappa hGamma seed hseed)
    (hext : ProtectedCardinalAssembly.ExtensionThroughFor Gamma kappa)
    {A0 : Set V} (hA0source : A0 ⊆ Gamma.source) (hA0card : #A0 ≤ kappa)
    (hA0Z : A0 ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed)
    {z : V} (hz : z ∈ A0) :
    ∃ (P : SafeStageTargetPath C (initialStage C) z)
      (U : ColouredSafeEndpointMovingStages.LimitClosure C
        (A0 ∪ Gamma.vertexSet P.ambientFamily)),
      U.closedSet ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed ∧
      C.movingReferenceDifference (initialStage C) U.later.stage ⊆ U.closedSet ∧
      let H := C.ladder.stageWeb (initialStage C)
      let X := H.vertexSet P.stageFamily
      IsLinkable ((H.delete X).retarget (C.ladder.frontier U.later.stage \ X)) := by
  obtain ⟨P, U, hUZ, hdiff⟩ := exists_safeInitialPath_and_containedClosure
    hkappa hGamma hUnhindered hseed C hC hA0source hA0card hA0Z hz
  refine ⟨P, U, hUZ, hdiff, ?_⟩
  apply C.isLinkable_retargetedStageResidual hext ?_ U.later.mem_club P
  apply lt_of_le_of_lt ?_ U.later.current_lt
  change (0 : Ordinal) ≤ C.newStage.1
  exact bot_le

#print axioms initial_movingReferenceDifference_subset_globalCarrier
#print axioms exists_initialEndpointLimitClosure_within_globalCarrier
#print axioms exists_safeInitialPath_and_containedClosure
#print axioms exists_safeInitialPath_closedResidual

end Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows
