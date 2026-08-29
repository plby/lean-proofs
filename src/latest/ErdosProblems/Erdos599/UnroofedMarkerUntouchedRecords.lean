/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerIndependentRoutes
import ErdosProblems.Erdos599.GroundingAllMarkerUntouchedGeometry

/-!
# Actual untouched grounded records on the unroofed ladder

The stationary good-index set minus all footprint-captured source indices
is still stationary. It supplies actual original-source records whose
whole carriers avoid every independently selected footprint and whose
physical supports miss the blocking separator.
-/

noncomputable section

namespace Erdos599.DWeb.UnroofedMarker

open Set Cardinal Order Ladder KappaLadder GroundingAllMarkerAuxiliary
open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} (G : DWeb V) (kappa : Cardinal.{u})
  (preferred : Stage kappa → Option V) (hNoEnter : G.NoEdgeEnters G.source)
  (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
  (hphi : Stationary.IsStationaryBelow kappa (ladder G kappa preferred).phi)

def auxiliaryUntouchedRecordIndices : Set (Stage kappa) :=
  (auxiliaryInput G kappa preferred hNoEnter).untouchedRecordIndices
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi)
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter)

theorem auxiliaryUntouchedRecordIndices_stationary : Stationary.IsStationaryBelow kappa
    (auxiliaryUntouchedRecordIndices G kappa preferred hNoEnter hkappa huncountable hphi) :=
  (auxiliaryInput G kappa preferred hNoEnter).untouchedRecordIndices_stationary
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi)
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter)

def AuxiliaryUntouchedRecord (i : GroundedRecord G kappa preferred) : Prop :=
  (auxiliaryInput G kappa preferred hNoEnter).UntouchedRecord
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi)
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter) i

theorem exists_untouched_grounded_record_of_mem_indices {a : Stage kappa}
    (ha : a ∈ auxiliaryUntouchedRecordIndices G kappa preferred hNoEnter hkappa huncountable hphi) :
    ∃ i : GroundedRecord G kappa preferred, groundedRecordStage G kappa preferred i = a ∧
      AuxiliaryUntouchedRecord G kappa preferred hNoEnter hkappa huncountable hphi i := by
  let A := auxiliaryInput G kappa preferred hNoEnter
  obtain ⟨i, hia, hi⟩ := A.exists_untouched_record_of_mem_indices
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi)
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter) ha
  refine ⟨i, ?_, hi⟩
  change groundedRecordStage G kappa preferred (A.sourceEquiv.symm (A.sourceEquiv i)) = a at hia
  rwa [Equiv.symm_apply_apply] at hia

/-- The untouched record is actual, begins in the original source, and
has no blocking point. No existence premise is left to the final theorem. -/
theorem exists_untouched_grounded_record : ∃ i : GroundedRecord G kappa preferred,
    AuxiliaryUntouchedRecord G kappa preferred hNoEnter hkappa huncountable hphi i ∧
      i.1.initial ∈ G.source ∧ Disjoint i.1.support
        (auxiliaryBlockingSet G kappa preferred hNoEnter hkappa huncountable hphi) := by
  obtain ⟨a, ha⟩ :=
    (auxiliaryUntouchedRecordIndices_stationary G kappa preferred hNoEnter
      hkappa huncountable hphi).nonempty
  obtain ⟨i, _hia, hi⟩ := exists_untouched_grounded_record_of_mem_indices
    G kappa preferred hNoEnter hkappa huncountable hphi ha
  refine ⟨i, hi, (groundedRecordStage_spec G kappa preferred i).2, ?_⟩
  exact (auxiliaryInput G kappa preferred hNoEnter).untouchedRecord_disjoint_blockingSet
    (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi)
    (auxiliary_record_initial_not_marker G kappa preferred hNoEnter) i hi

theorem auxiliaryUntouchedRecord_carrier_disjoint_footprint (i : GroundedRecord G kappa preferred)
    (hi : AuxiliaryUntouchedRecord G kappa preferred hNoEnter hkappa huncountable hphi i)
    (r : auxiliaryRequests G kappa preferred hNoEnter hkappa huncountable hphi) :
    Disjoint ((auxiliaryInput G kappa preferred hNoEnter).recordCarrier i)
      ((auxiliaryInput G kappa preferred hNoEnter).routeFootprint
        (auxiliaryPopularSeparator G kappa preferred hNoEnter hkappa huncountable hphi).cut
        (auxiliaryIndependentPath G kappa preferred hNoEnter hkappa huncountable hphi r)) := hi.2 r

#print axioms auxiliaryUntouchedRecordIndices_stationary
#print axioms exists_untouched_grounded_record_of_mem_indices
#print axioms exists_untouched_grounded_record
#print axioms auxiliaryUntouchedRecord_carrier_disjoint_footprint

end Erdos599.DWeb.UnroofedMarker
