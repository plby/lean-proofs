/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerIndependentSelection

/-!
# Physical fragment independence of the selected auxiliary routes

Footprint disjointness is stronger than disjoint auxiliary paths. It
forces actual touched fragment supports to be disjoint, and keeps every
other route's touched fragments away from a selected good origin record.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I) {kappa : Cardinal.{u}}
  {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
  (hInitial : ∀ i, (L.record i).initial ∉ L.markers)

theorem independentSelectedPath_finish (r : L.Request S.cut) :
    (L.independentSelectedPath S hInitial r).finish = r.1 :=
  (L.shortenedRecordFan S r hInitial).ends_in_join (L.independentSelectedPath_mem S hInitial r)

theorem independentSelectedPath_start_good_record (r : L.Request S.cut) :
    ∃ i : I, (L.independentSelectedPath S hInitial r).start = Vertex.source i ∧
      i ∉ L.badRecords S.cut :=
  L.shortenedRecordFan_start_good_record S r hInitial (L.independentSelectedPath_mem S hInitial r)

theorem independentSelectedPath_met_fragments_disjoint
    (r s : L.Request S.cut) (hrs : r ≠ s)
    {P Q : L.CutFragment} (hP : P ∈ L.cutFragments S.cut) (hQ : Q ∈ L.cutFragments S.cut)
    (e f : {e : V × V // e ∈ familyEdges L.reference.paths})
    (heP : e.1 ∈ P.path.edgeSet) (hfQ : f.1 ∈ Q.path.edgeSet)
    (heRoute : Vertex.edge e ∈ (L.independentSelectedPath S hInitial r).support)
    (hfRoute : Vertex.edge f ∈ (L.independentSelectedPath S hInitial s).support) :
    Disjoint P.path.support Q.path.support := by
  apply Set.disjoint_left.mpr
  intro x hxP hxQ
  have hCarriers := L.fragmentCarrier_eq_of_common S.cut hP hQ hxP hxQ
  have heQ : Vertex.edge e ∈ L.fragmentCarrier S.cut Q :=
    hCarriers ▸ (show Vertex.edge e ∈ L.fragmentCarrier S.cut P from heP)
  have heFootR := L.support_subset_routeFootprint S.cut
    (L.independentSelectedPath S hInitial r) heRoute
  have heFootS := L.fragmentCarrier_subset_routeFootprint S.cut
    (L.independentSelectedPath S hInitial s) hQ f hfQ hfRoute heQ
  exact Set.disjoint_left.mp (L.independentSelectedPath_footprints_disjoint S hInitial hrs)
    heFootR heFootS

/-- This includes an origin record which is a singleton and has no edge
gadget: its source tag still witnesses a forbidden footprint collision. -/
theorem independentSelectedPath_origin_disjoint_met_fragment
    (r s : L.Request S.cut) (hrs : r ≠ s) (i : I)
    (hi : i ∉ L.badRecords S.cut)
    (hri : (L.independentSelectedPath S hInitial r).start = .source i)
    {P : L.CutFragment} (hP : P ∈ L.cutFragments S.cut)
    (e : {e : V × V // e ∈ familyEdges L.reference.paths}) (heP : e.1 ∈ P.path.edgeSet)
    (heRoute : Vertex.edge e ∈ (L.independentSelectedPath S hInitial s).support) :
    Disjoint (L.record i).support P.path.support := by
  apply Set.disjoint_left.mpr
  intro x hxi hxP
  have hparent : P.parent = L.record i := DWeb.IsWarp.eq_of_mem_support L.reference.disjoint
    P.parent_mem (L.record_mem i) (P.support_subset hxP) hxi
  have hCarriers := L.fragmentCarrier_eq_recordCarrier S.cut hP i hi hparent
  have hiP : Vertex.source i ∈ L.fragmentCarrier S.cut P :=
    hCarriers.symm ▸ (show Vertex.source i ∈ L.recordCarrier i from rfl)
  have hiFootR := L.recordCarrier_subset_routeFootprint S.cut
    (L.independentSelectedPath S hInitial r) i hi hri (show Vertex.source i ∈ L.recordCarrier i from rfl)
  have hiFootS := L.fragmentCarrier_subset_routeFootprint S.cut
    (L.independentSelectedPath S hInitial s) hP e heP heRoute hiP
  exact Set.disjoint_left.mp (L.independentSelectedPath_footprints_disjoint S hInitial hrs)
    hiFootR hiFootS

#print axioms independentSelectedPath_finish
#print axioms independentSelectedPath_met_fragments_disjoint
#print axioms independentSelectedPath_origin_disjoint_met_fragment

end Erdos599.GroundingAllMarkerAuxiliary.Input
