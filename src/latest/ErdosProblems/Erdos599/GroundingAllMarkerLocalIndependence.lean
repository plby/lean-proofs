/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerLocalSupport

/-!
# Pairwise disjoint physical regions of the local transactions

Independent auxiliary footprints control whole good origins and all
touched grounded fragments. Request fragments are hanging, so they miss
every touched grounded fragment; different requests have different
fragment initials. Off-reference vertices are controlled by route
disjointness. These are physical support statements in the original graph.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I) {kappa : Cardinal.{u}}
  {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
  (hInitial : ∀ i, (L.record i).initial ∉ L.markers)
  (hInitials : G.initialSet L.reference.paths ⊆ G.source ∪ L.markers)
  (hNoEnter : G.NoEdgeEnters G.source) (hMarkers : Disjoint G.source L.markers)

include hNoEnter hMarkers in
private theorem grounded_disjoint_requestFragment {P Q : L.CutFragment}
    (hP : P ∈ L.cutFragments S.cut) (hQ : Q ∈ L.cutFragments S.cut)
    (hground : L.CutFragmentGrounded P) (r : L.Request S.cut)
    (hinit : Q.path.initial = L.requestVertex r) : Disjoint P.path.support Q.path.support := by
  apply Set.disjoint_left.mpr
  intro x hxP hxQ
  have heq := L.cutFragment_initial_eq_of_common S.cut hP hQ hxP hxQ
  have hQsource : Q.path.initial ∈ G.source := heq ▸
    (show P.path.initial ∈ G.source from hground)
  exact L.requestFragment_not_grounded S.cut r hNoEnter hMarkers Q hinit hQsource

include hInitials hNoEnter hMarkers in
theorem independentLocalFragments_disjoint (r s : L.Request S.cut) (hrs : r ≠ s)
    {P Q : L.CutFragment}
    (hP : P ∈ L.localFragments S.cut (L.independentSelectedPath S hInitial r) r)
    (hQ : Q ∈ L.localFragments S.cut (L.independentSelectedPath S hInitial s) s) :
    Disjoint P.path.support Q.path.support := by
  rcases hP with ⟨e, rfl⟩ | hP
  · rcases hQ with ⟨f, rfl⟩ | hQ
    · exact L.independentSelectedPath_met_fragments_disjoint S hInitial r s hrs
        (L.routeFragment_mem S.cut _ e) (L.routeFragment_mem S.cut _ f) e.1 f.1
        (L.routeFragment_edge S.cut _ e) (L.routeFragment_edge S.cut _ f) e.2.1 f.2.1
    · exact grounded_disjoint_requestFragment L S hNoEnter hMarkers
        (L.routeFragment_mem S.cut _ e) (L.selectedRequestFragments_spec S.cut s hQ).1
        (L.routeFragment_grounded S hInitial hInitials r
          (L.independentSelectedPath_mem S hInitial r) e)
        s (L.selectedRequestFragments_spec S.cut s hQ).2
  · rcases hQ with ⟨f, rfl⟩ | hQ
    · exact (grounded_disjoint_requestFragment L S hNoEnter hMarkers
        (L.routeFragment_mem S.cut _ f) (L.selectedRequestFragments_spec S.cut r hP).1
        (L.routeFragment_grounded S hInitial hInitials s
          (L.independentSelectedPath_mem S hInitial s) f)
        r (L.selectedRequestFragments_spec S.cut r hP).2).symm
    · apply Set.disjoint_left.mpr
      intro x hxP hxQ
      have hPs := L.selectedRequestFragments_spec S.cut r hP
      have hQs := L.selectedRequestFragments_spec S.cut s hQ
      have heq := L.cutFragment_initial_eq_of_common S.cut hPs.1 hQs.1 hxP hxQ
      exact hrs (L.requestVertex_injective S.cut (hPs.2.symm.trans (heq.trans hQs.2)))

theorem independentOrigin_disjoint_localFragment (r s : L.Request S.cut) (hrs : r ≠ s)
    {P : L.CutFragment}
    (hP : P ∈ L.localFragments S.cut (L.independentSelectedPath S hInitial s) s) :
    Disjoint (L.record (L.independentPortAugmentation S hInitial r).origin).support
      P.path.support := by
  let D := L.independentPortAugmentation S hInitial r
  rcases hP with ⟨e, rfl⟩ | hP
  · exact L.independentSelectedPath_origin_disjoint_met_fragment S hInitial r s hrs
      D.origin D.origin_good D.origin_start (L.routeFragment_mem S.cut _ e) e.1
      (L.routeFragment_edge S.cut _ e) e.2.1
  · exact L.good_record_disjoint_request_fragment S hInitial s D.origin D.origin_good P
      (L.selectedRequestFragments_spec S.cut s hP).2

theorem independentOrigins_disjoint (r s : L.Request S.cut) (hrs : r ≠ s) :
    Disjoint (L.record (L.independentPortAugmentation S hInitial r).origin).support
      (L.record (L.independentPortAugmentation S hInitial s).origin).support := by
  let D := L.independentPortAugmentation S hInitial r
  let F := L.independentPortAugmentation S hInitial s
  apply Set.disjoint_left.mpr
  intro x hxD hxF
  have hi := L.record_injective (DWeb.IsWarp.eq_of_mem_support L.reference.disjoint
    (L.record_mem D.origin) (L.record_mem F.origin) hxD hxF)
  have hsR := L.recordCarrier_subset_routeFootprint S.cut
    (L.independentSelectedPath S hInitial r) D.origin D.origin_good D.origin_start
    (show Vertex.source D.origin ∈ L.recordCarrier D.origin from rfl)
  have hsS := L.recordCarrier_subset_routeFootprint S.cut
    (L.independentSelectedPath S hInitial s) F.origin F.origin_good F.origin_start
    (show Vertex.source F.origin ∈ L.recordCarrier F.origin from rfl)
  exact Set.disjoint_left.mp (L.independentSelectedPath_footprints_disjoint S hInitial hrs)
    hsR (hi.symm ▸ hsS)

private theorem localReference_mem_reference (r : L.Request S.cut) {x : V}
    (hx : x ∈ (L.record (L.independentPortAugmentation S hInitial r).origin).support ∪
      {x | ∃ P ∈ L.localFragments S.cut (L.independentSelectedPath S hInitial r) r,
        x ∈ P.path.support}) : x ∈ G.vertexSet L.reference.paths := by
  rcases hx with hx | ⟨P, _, hxP⟩
  · exact ⟨_, L.record_mem _, hx⟩
  · exact ⟨P.parent, P.parent_mem, P.support_subset hxP⟩

include hInitials hNoEnter hMarkers in
theorem independentLocalRegions_disjoint (r s : L.Request S.cut) (hrs : r ≠ s) :
    Disjoint ((L.independentPortAugmentation S hInitial r).localRegion L)
      ((L.independentPortAugmentation S hInitial s).localRegion L) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases hx with hx | ⟨hxOff, hxTag⟩
  · rcases hy with hy | ⟨hyOff, _⟩
    · rcases hx with hx | ⟨P, hP, hxP⟩
      · rcases hy with hy | ⟨Q, hQ, hxQ⟩
        · exact Set.disjoint_left.mp (L.independentOrigins_disjoint S hInitial r s hrs) hx hy
        · exact Set.disjoint_left.mp
            (L.independentOrigin_disjoint_localFragment S hInitial r s hrs hQ) hx hxQ
      · rcases hy with hy | ⟨Q, hQ, hxQ⟩
        · exact Set.disjoint_left.mp
            (L.independentOrigin_disjoint_localFragment S hInitial s r hrs.symm hP) hy hxP
        · exact Set.disjoint_left.mp
            (L.independentLocalFragments_disjoint S hInitial hInitials hNoEnter hMarkers
              r s hrs hP hQ) hxP hxQ
    · exact hyOff (localReference_mem_reference L S hInitial r hx)
  · rcases hy with hy | ⟨_, hyTag⟩
    · exact hxOff (localReference_mem_reference L S hInitial s hy)
    · exact Set.disjoint_left.mp (L.independentSelectedPath_footprints_disjoint S hInitial hrs)
        (L.support_subset_routeFootprint S.cut _ hxTag)
        (L.support_subset_routeFootprint S.cut _ hyTag)

#print axioms independentLocalFragments_disjoint
#print axioms independentOrigins_disjoint
#print axioms independentLocalRegions_disjoint

theorem untouchedRecord_disjoint_localRegion (i : I) (hi : L.UntouchedRecord S hInitial i)
    (r : L.Request S.cut) :
    Disjoint (L.record i).support
      ((L.independentPortAugmentation S hInitial r).localRegion L) := by
  apply Set.disjoint_left.mpr
  intro x hxi hx
  rcases hx with (hOrigin | ⟨P, hP, hxP⟩) | ⟨hxOff, _⟩
  · exact Set.disjoint_left.mp (L.untouchedRecord_disjoint_selected_origin S hInitial i hi r
      _ (L.independentPortAugmentation S hInitial r).origin_start) hxi hOrigin
  · rcases hP with ⟨e, rfl⟩ | hP
    · exact Set.disjoint_left.mp (L.untouchedRecord_disjoint_met_fragment S hInitial i hi r
        (L.routeFragment_mem S.cut _ e) e.1 (L.routeFragment_edge S.cut _ e) e.2.1) hxi hxP
    · exact Set.disjoint_left.mp (L.good_record_disjoint_request_fragment S hInitial r i hi.1
        P (L.selectedRequestFragments_spec S.cut r hP).2) hxi hxP
  · exact hxOff ⟨L.record i, L.record_mem i, hxi⟩

#print axioms untouchedRecord_disjoint_localRegion

end Erdos599.GroundingAllMarkerAuxiliary.Input
