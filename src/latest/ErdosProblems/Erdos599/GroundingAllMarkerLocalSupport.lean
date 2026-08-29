/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerLocalWarp

/-!
# Physical confinement of a local grounding family

The support bound consists of the whole good origin, selected surviving
fragments, and off-reference route vertices. Stopping affects the actual
edges, not this upper bound. The route graph's port provenance controls
inserted edges, including final cut-edge and marker requests.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

def offRouteVertices (q : FinitePath L.web.graph) : Set V :=
  {x | ∃ hx : x ∉ G.vertexSet L.reference.paths, Vertex.off ⟨x, hx⟩ ∈ q.support}

namespace PortAugmentation

variable {C : Set L.Vertex} {q : FinitePath L.web.graph} {r : L.Request C}
  (D : L.PortAugmentation C q r)

def localRegion : Set V := (L.record D.origin).support ∪
  {x | ∃ P ∈ L.localFragments C q r, x ∈ P.path.support} ∪ L.offRouteVertices q

theorem localBaseEdges_endpoints {x y : V} (he : (x, y) ∈ D.localBaseEdges L) :
    x ∈ D.localRegion L ∧ y ∈ D.localRegion L := by
  rcases he.1.2.resolve_left he.2 with hp | ⟨P, hP, heP⟩
  · have hxy := (D.originPrefix L).edgeSet_subset_support_prod hp
    exact ⟨Or.inl (Or.inl ((D.originPrefix_spec L).2.2.1 hxy.1)),
      Or.inl (Or.inl ((D.originPrefix_spec L).2.2.1 hxy.2))⟩
  · have hxy := (L.stoppedFragment C P).edgeSet_subset_support_prod heP
    exact ⟨Or.inl (Or.inr ⟨P, hP, L.stoppedFragment_support_subset C P hxy.1⟩),
      Or.inl (Or.inr ⟨P, hP, L.stoppedFragment_support_subset C P hxy.2⟩)⟩

end PortAugmentation

variable {kappa : Cardinal.{u}} {U : Popular.KappaIndexed L.web kappa}
  (S : Popular.PopularSeparator U) (hInitial : ∀ i, (L.record i).initial ∉ L.markers)

namespace PortAugmentation

variable (r : L.Request S.cut) {q : FinitePath L.web.graph}
  (hq : q ∈ (L.shortenedRecordFan S r hInitial).paths) (D : L.PortAugmentation S.cut q r)

include hq in
theorem requestVertex_mem_localRegion : L.requestVertex r ∈ D.localRegion L := by
  by_cases hr : L.requestVertex r ∈ G.vertexSet L.reference.paths
  · obtain ⟨P, hP⟩ := L.selectedRequestFragments_nonempty S.cut r hr
    exact Or.inl (Or.inr ⟨P, Or.inr hP,
      (L.selectedRequestFragments_spec S.cut r hP).2 ▸ P.path.initial_mem_support⟩)
  · have hrecv := L.request_receiving r
    rcases L.request_cases r with ⟨y, hry⟩ | ⟨e, hre⟩ | ⟨z, hrz⟩
    · have hy : y.1 = L.requestVertex r :=
        Option.some.inj (by simpa only [hry, receiving] using hrecv)
      obtain ⟨P, hP, hPy⟩ := L.markers_initial y.2
      exact (hr ⟨P, hP, hPy.trans hy ▸ P.initial_mem_support⟩).elim
    · have he : e.1.2 = L.requestVertex r :=
        Option.some.inj (by simpa only [hre, receiving] using hrecv)
      exact (hr (he ▸ (familyEdges_subset_vertexSet_prod L.reference.paths e.2).2)).elim
    · have hz : z.1 = L.requestVertex r :=
        Option.some.inj (by simpa only [hrz, receiving] using hrecv)
      have hmem : Vertex.off z ∈ q.support :=
        hrz ▸ (L.shortenedRecordFan S r hInitial).ends_in_join hq ▸ q.finish_mem_support
      exact Or.inr ⟨hr, by simpa only [← hz] using hmem⟩

include hq in
theorem sending_mem_localRegion {a : L.Vertex} (ha : a ∈ q.support) (har : a ≠ r.1)
    {x : V} (hs : L.sending a = some x) : x ∈ D.localRegion L := by
  cases a with
  | source i =>
      have hstart : Vertex.source i = q.start := by
        by_contra hne
        obtain ⟨b, hb⟩ := FinitePath.exists_incoming_edge_of_mem_support_of_ne_start q ha hne
        exact L.not_adj_to_source b i (q.edgeSet_subset_adj hb)
      have hi : i = D.origin := Vertex.source.inj (hstart.trans D.origin_start)
      exact Or.inl (Or.inl (hi ▸ G.terminal_mem_support hs))
  | marker y => simp [sending] at hs
  | off z =>
      have hz : z.1 = x := Option.some.inj hs
      exact hz ▸ Or.inr ⟨z.2, ha⟩
  | edge e =>
      have huncut : e.1 ∉ L.cutEdges S.cut := fun hc ↦
        har (L.shortenedRecordFan_cut_normalized S r hInitial hq ⟨ha, hc.2⟩)
      let t : L.RouteEdge S.cut q := ⟨e, ha, huncut⟩
      have hx := ((L.routeFragment S.cut q t).path.edgeSet_subset_support_prod
        (L.routeFragment_edge S.cut q t)).1
      exact Or.inl (Or.inr ⟨L.routeFragment S.cut q t, Or.inl ⟨t, rfl⟩,
        Option.some.inj hs ▸ hx⟩)

include hq in
theorem receiving_mem_localRegion {a : L.Vertex} (ha : a ∈ q.support)
    {x : V} (hr : L.receiving a = some x) : x ∈ D.localRegion L := by
  by_cases har : a = r.1
  · have hx : x = L.requestVertex r :=
      Option.some.inj (hr.symm.trans (har ▸ L.request_receiving r))
    exact hx.symm ▸ D.requestVertex_mem_localRegion L S hInitial r hq
  cases a with
  | source i => simp [receiving] at hr
  | marker y =>
      have hne : Vertex.marker y ≠ q.finish := fun h ↦
        har (h.trans ((L.shortenedRecordFan S r hInitial).ends_in_join hq))
      obtain ⟨b, hb⟩ := FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish q ha hne
      exact (L.not_adj_from_marker y b (q.edgeSet_subset_adj hb)).elim
  | off z =>
      have hz : z.1 = x := Option.some.inj hr
      exact hz ▸ Or.inr ⟨z.2, ha⟩
  | edge e =>
      have huncut : e.1 ∉ L.cutEdges S.cut := fun hc ↦
        har (L.shortenedRecordFan_cut_normalized S r hInitial hq ⟨ha, hc.2⟩)
      let t : L.RouteEdge S.cut q := ⟨e, ha, huncut⟩
      have hx := ((L.routeFragment S.cut q t).path.edgeSet_subset_support_prod
        (L.routeFragment_edge S.cut q t)).2
      exact Or.inl (Or.inr ⟨L.routeFragment S.cut q t, Or.inl ⟨t, rfl⟩,
        Option.some.inj hr ▸ hx⟩)

theorem localSwitchedEdges_endpoints {x y : V}
    (he : (x, y) ∈ D.localSwitchedEdges L S hInitial r hq) :
    x ∈ D.localRegion L ∧ y ∈ D.localRegion L := by
  rcases he with ⟨he | he, hne⟩
  · exact D.localBaseEdges_endpoints L ⟨he.1, hne⟩
  · have hports := (D.path.edgeSet_subset_adj he).2
    constructor
    · rcases hports.1 with hx | ⟨a, ha, har, hs⟩
      · have hx' : x = D.departure := hx
        exact Or.inl (Or.inl (hx'.symm ▸ D.departure_mem))
      · exact D.sending_mem_localRegion L S hInitial r hq ha har hs
    · obtain ⟨a, ha, hr⟩ := hports.2
      exact D.receiving_mem_localRegion L S hInitial r hq ha hr

include hq in
theorem localBlockingSet_subset_localRegion : D.localBlockingSet L ⊆ D.localRegion L := by
  rintro x ⟨_, hx | ⟨P, hP, hxP⟩⟩
  · exact hx.symm ▸ D.requestVertex_mem_localRegion L S hInitial r hq
  · exact Or.inl (Or.inr ⟨P, hP, hxP⟩)

variable (hInitials : G.initialSet L.reference.paths ⊆ G.source ∪ L.markers)
  (hOrigin : (L.record D.origin).initial ∈ G.source)

theorem localGroundingWarp_support_subset {p : FinitePath G.graph}
    (hp : p ∈ (D.localGroundingWarp L S hInitial hInitials r hq hOrigin).paths) :
    p.support ⊆ D.localRegion L := by
  intro x hx
  by_cases hfinish : x = p.finish
  · exact hfinish.symm ▸ D.localBlockingSet_subset_localRegion L S hInitial r hq
      ((D.localGroundingWarp L S hInitial hInitials r hq hOrigin).ends_in_target hp)
  · obtain ⟨y, hy⟩ := FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish p hx hfinish
    exact (D.localSwitchedEdges_endpoints L S hInitial r hq
      (D.localGroundingWarp_edges L S hInitial hInitials r hq hOrigin hp hy)).1

#print axioms requestVertex_mem_localRegion
#print axioms localSwitchedEdges_endpoints
#print axioms localGroundingWarp_support_subset

end PortAugmentation
end Erdos599.GroundingAllMarkerAuxiliary.Input
