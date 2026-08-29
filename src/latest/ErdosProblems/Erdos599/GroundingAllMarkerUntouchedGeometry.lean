/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerUntouchedRecords

/-!
# Physical avoidance by an untouched good record

Whole-carrier avoidance excludes every represented route port, every
touched surviving fragment and each selected origin record. Cut requests
cannot receive on any good record, so their attached fragments avoid it
as well. Finally every good record misses the actual blocking set.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I) {kappa : Cardinal.{u}}
  {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
  (hInitial : ∀ i, (L.record i).initial ∉ L.markers)

include hInitial in
theorem requestVertex_not_mem_good_record (r : L.Request S.cut) (i : I)
    (hi : i ∉ L.badRecords S.cut) : L.requestVertex r ∉ (L.record i).support := by
  intro hx
  have hrOwn := L.receiving_mem_recordCarrier i (hInitial i) (L.request_receiving r) hx
  exact L.goodRecordFan_request_not_in_origin_carrier S r hi hrOwn

include hInitial in
theorem good_record_disjoint_request_fragment (r : L.Request S.cut) (i : I)
    (hi : i ∉ L.badRecords S.cut) (P : L.CutFragment)
    (hinit : P.path.initial = L.requestVertex r) :
    Disjoint (L.record i).support P.path.support := by
  apply Set.disjoint_left.mpr
  intro x hxi hxP
  have hparent : P.parent = L.record i := DWeb.IsWarp.eq_of_mem_support L.reference.disjoint
    P.parent_mem (L.record_mem i) (P.support_subset hxP) hxi
  have hentry : L.requestVertex r ∈ (L.record i).support :=
    hinit ▸ hparent ▸ P.support_subset P.path.initial_mem_support
  exact L.requestVertex_not_mem_good_record S hInitial r i hi hentry

theorem untouchedRecord_disjoint_met_fragment (i : I) (hi : L.UntouchedRecord S hInitial i)
    (r : L.Request S.cut) {P : L.CutFragment} (hP : P ∈ L.cutFragments S.cut)
    (e : {e : V × V // e ∈ familyEdges L.reference.paths}) (heP : e.1 ∈ P.path.edgeSet)
    (heRoute : Vertex.edge e ∈ (L.independentSelectedPath S hInitial r).support) :
    Disjoint (L.record i).support P.path.support := by
  apply Set.disjoint_left.mpr
  intro x hxi hxP
  have hparent : P.parent = L.record i := DWeb.IsWarp.eq_of_mem_support L.reference.disjoint
    P.parent_mem (L.record_mem i) (P.support_subset hxP) hxi
  have hCarriers := L.fragmentCarrier_eq_recordCarrier S.cut hP i hi.1 hparent
  have hiP : Vertex.source i ∈ L.fragmentCarrier S.cut P :=
    hCarriers.symm ▸ (show Vertex.source i ∈ L.recordCarrier i from rfl)
  have hiFoot := L.fragmentCarrier_subset_routeFootprint S.cut
    (L.independentSelectedPath S hInitial r) hP e heP heRoute hiP
  exact Set.disjoint_left.mp (hi.2 r) (show Vertex.source i ∈ L.recordCarrier i from rfl) hiFoot

theorem untouchedRecord_disjoint_selected_origin (i : I) (hi : L.UntouchedRecord S hInitial i)
    (r : L.Request S.cut) (j : I)
    (hj : (L.independentSelectedPath S hInitial r).start = .source j) :
    Disjoint (L.record i).support (L.record j).support := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hij : i = j := L.record_injective (DWeb.IsWarp.eq_of_mem_support L.reference.disjoint
    (L.record_mem i) (L.record_mem j) hxi hxj)
  subst j
  have hiRoute : Vertex.source i ∈ (L.independentSelectedPath S hInitial r).support :=
    hj ▸ (L.independentSelectedPath S hInitial r).start_mem_support
  exact Set.disjoint_left.mp (L.untouchedRecord_carrier_disjoint_route S hInitial i hi r)
    (show Vertex.source i ∈ L.recordCarrier i from rfl) hiRoute

theorem untouchedRecord_avoids_route_ports (i : I) (hi : L.UntouchedRecord S hInitial i)
    (r : L.Request S.cut) {a : L.Vertex}
    (ha : a ∈ (L.independentSelectedPath S hInitial r).support)
    {x : V} (hx : x ∈ (L.record i).support) :
    L.sending a ≠ some x ∧ L.receiving a ≠ some x := by
  have hdisj := L.untouchedRecord_carrier_disjoint_route S hInitial i hi r
  constructor
  · intro hsend
    obtain ⟨b, hb, hbsend⟩ := L.exists_recordCarrier_sending i hx
    have hab : a = b := L.sending_unique hsend hbsend
    exact Set.disjoint_left.mp hdisj (hab.symm ▸ hb) ha
  · intro hreceive
    exact Set.disjoint_left.mp hdisj
      (L.receiving_mem_recordCarrier i (hInitial i) hreceive hx) ha

theorem untouchedRecord_disjoint_blockingSet (i : I) (hi : L.UntouchedRecord S hInitial i) :
    Disjoint (L.record i).support (L.blockingSet S.cut) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxK
  exact Set.disjoint_left.mp (L.goodRecordVertices_disjoint_blockingSet S.cut S.separates)
    ⟨i, hi.1, hxi⟩ hxK

#print axioms good_record_disjoint_request_fragment
#print axioms untouchedRecord_disjoint_met_fragment
#print axioms untouchedRecord_disjoint_selected_origin
#print axioms untouchedRecord_avoids_route_ports
#print axioms untouchedRecord_disjoint_blockingSet

end Erdos599.GroundingAllMarkerAuxiliary.Input
