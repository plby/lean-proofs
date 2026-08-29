/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerFootprintReachability

/-!
# Stationarily many good records remain wholly untouched

Remove all source indices captured by any selected footprint, not just
the starts of the selected paths. The remaining good indices are still
stationary. Carrier closure upgrades absence of a source tag to avoidance
of its entire carrier by every footprint.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts Stationary

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I) {kappa : Cardinal.{u}}
  {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
  (hInitial : ∀ i, (L.record i).initial ∉ L.markers)

def untouchedRecordIndices : Set (Below kappa) :=
  L.goodRecordIndices U S.cut \ L.usedFootprintIndices S hInitial

theorem untouchedRecordIndices_stationary :
    IsStationaryBelow kappa (L.untouchedRecordIndices S hInitial) :=
  PopularSwitching.stationary_diff_of_stationary_of_nonstationary
    U.regular U.uncountable (L.goodRecordIndices_stationary U S)
    (L.usedFootprintIndices_nonstationary S hInitial)

def UntouchedRecord (i : I) : Prop := i ∉ L.badRecords S.cut ∧
  ∀ r : L.Request S.cut, Disjoint (L.recordCarrier i)
    (L.routeFootprint S.cut (L.independentSelectedPath S hInitial r))

theorem recordCarrier_disjoint_footprint_of_index_not_used (i : I)
    (hi : i ∉ L.badRecords S.cut)
    (hindex : U.f (L.sourceEquiv i) ∉ L.usedFootprintIndices S hInitial)
    (r : L.Request S.cut) : Disjoint (L.recordCarrier i)
      (L.routeFootprint S.cut (L.independentSelectedPath S hInitial r)) := by
  apply Set.disjoint_left.mpr
  intro a hai haFoot
  have hcarrier := L.vertexFragmentCarrier_eq_recordCarrier_of_mem S.cut i hi hai
  have hiCarrier : Vertex.source i ∈ L.vertexFragmentCarrier S.cut a := by
    rw [hcarrier]
    exact rfl
  have hiFoot := L.routeFootprint_closed S.cut
    (L.independentSelectedPath S hInitial r) haFoot hiCarrier
  exact hindex ⟨r, L.sourceEquiv i, hiFoot, rfl⟩

theorem exists_untouched_record_of_mem_indices {a : Below kappa}
    (ha : a ∈ L.untouchedRecordIndices S hInitial) :
    ∃ i : I, U.f (L.sourceEquiv i) = a ∧ L.UntouchedRecord S hInitial i := by
  obtain ⟨i, hia, hiSource, hiEdges⟩ := L.exists_uncut_record_of_mem_goodRecordIndices U S.cut ha.1
  have hiGood : i ∉ L.badRecords S.cut := by
    rintro (hsrc | ⟨e, he, heC⟩)
    · exact hiSource hsrc
    · exact Set.disjoint_left.mp hiEdges he heC
  refine ⟨i, hia, hiGood, ?_⟩
  intro r
  apply L.recordCarrier_disjoint_footprint_of_index_not_used S hInitial i hiGood
  simpa only [hia] using ha.2

theorem exists_untouched_record : ∃ i : I, L.UntouchedRecord S hInitial i := by
  obtain ⟨a, ha⟩ := (L.untouchedRecordIndices_stationary S hInitial).nonempty
  obtain ⟨i, _hiIndex, hi⟩ := L.exists_untouched_record_of_mem_indices S hInitial ha
  exact ⟨i, hi⟩

theorem untouchedRecord_carrier_disjoint_route (i : I) (hi : L.UntouchedRecord S hInitial i)
    (r : L.Request S.cut) :
    Disjoint (L.recordCarrier i) (L.independentSelectedPath S hInitial r).support :=
  (hi.2 r).mono_right (L.support_subset_routeFootprint S.cut _)

#print axioms untouchedRecordIndices_stationary
#print axioms exists_untouched_record_of_mem_indices
#print axioms exists_untouched_record
#print axioms untouchedRecord_carrier_disjoint_route

end Erdos599.GroundingAllMarkerAuxiliary.Input
