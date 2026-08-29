/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerFragmentCarriers

/-!
# Countable fragmentwise footprints of auxiliary routes

Each uncut edge gadget expands to its actual surviving fragment carrier;
each good source expands to its whole uncut record carrier. Other vertices
do not expand. The footprint adds these carriers to the finite route.
It is countable and has no new cut contacts, so other requests remain
available throughout the later independent-route recursion.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

def edgeFragment (C : Set L.Vertex)
    (e : {e : V × V // e ∈ familyEdges L.reference.paths}) (he : e.1 ∉ L.cutEdges C) :
    L.CutFragment := Classical.choose (L.exists_cutFragment_containing_edge C e.2 he)

theorem edgeFragment_mem (C : Set L.Vertex)
    (e : {e : V × V // e ∈ familyEdges L.reference.paths}) (he : e.1 ∉ L.cutEdges C) :
    L.edgeFragment C e he ∈ L.cutFragments C :=
  (Classical.choose_spec (L.exists_cutFragment_containing_edge C e.2 he)).1

theorem edgeFragment_edge (C : Set L.Vertex)
    (e : {e : V × V // e ∈ familyEdges L.reference.paths}) (he : e.1 ∉ L.cutEdges C) :
    e.1 ∈ (L.edgeFragment C e he).path.edgeSet :=
  (Classical.choose_spec (L.exists_cutFragment_containing_edge C e.2 he)).2

def vertexFragmentCarrier (C : Set L.Vertex) : L.Vertex → Set L.Vertex := by
  classical
  exact fun
    | .source i => if i ∉ L.badRecords C then L.recordCarrier i else ∅
    | .edge e => if he : e.1 ∉ L.cutEdges C then L.fragmentCarrier C (L.edgeFragment C e he) else ∅
    | _ => ∅

theorem vertexFragmentCarrier_countable (C : Set L.Vertex) (a : L.Vertex) :
    (L.vertexFragmentCarrier C a).Countable := by
  classical
  cases a with
  | source i =>
      by_cases hi : i ∉ L.badRecords C
      · simpa only [vertexFragmentCarrier, if_pos hi] using L.recordCarrier_countable i
      · simpa only [vertexFragmentCarrier, if_neg hi] using
          (Set.countable_empty : (∅ : Set L.Vertex).Countable)
  | edge e =>
      by_cases he : e.1 ∉ L.cutEdges C
      · simpa only [vertexFragmentCarrier, dif_pos he] using
          L.fragmentCarrier_countable C (L.edgeFragment C e he)
      · simpa only [vertexFragmentCarrier, dif_neg he] using
          (Set.countable_empty : (∅ : Set L.Vertex).Countable)
  | marker y => exact Set.countable_empty
  | off x => exact Set.countable_empty

theorem vertexFragmentCarrier_disjoint_cut (C : Set L.Vertex) (a : L.Vertex) :
    Disjoint (L.vertexFragmentCarrier C a) C := by
  classical
  cases a with
  | source i =>
      by_cases hi : i ∉ L.badRecords C
      · simpa only [vertexFragmentCarrier, if_pos hi] using
          L.recordCarrier_disjoint_cut_of_not_bad C hi
      · simpa only [vertexFragmentCarrier, if_neg hi] using Set.empty_disjoint C
  | edge e =>
      by_cases he : e.1 ∉ L.cutEdges C
      · simpa only [vertexFragmentCarrier, dif_pos he] using
          L.fragmentCarrier_disjoint_cut C (L.edgeFragment_mem C e he)
      · simpa only [vertexFragmentCarrier, dif_neg he] using Set.empty_disjoint C
  | marker y => exact Set.empty_disjoint _
  | off x => exact Set.empty_disjoint _

def routeFootprint (C : Set L.Vertex) (p : FinitePath L.web.graph) : Set L.Vertex :=
  p.support ∪ ⋃ a ∈ p.support, L.vertexFragmentCarrier C a

theorem support_subset_routeFootprint (C : Set L.Vertex) (p : FinitePath L.web.graph) :
    p.support ⊆ L.routeFootprint C p := Set.subset_union_left

theorem vertexFragmentCarrier_subset_routeFootprint (C : Set L.Vertex)
    (p : FinitePath L.web.graph) {a : L.Vertex} (ha : a ∈ p.support) :
    L.vertexFragmentCarrier C a ⊆ L.routeFootprint C p := by
  intro b hb
  exact Or.inr (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, hb⟩⟩)

theorem routeFootprint_countable (C : Set L.Vertex) (p : FinitePath L.web.graph) :
    (L.routeFootprint C p).Countable :=
  p.support_finite.countable.union (p.support_finite.countable.biUnion
    (fun a _ ↦ L.vertexFragmentCarrier_countable C a))

theorem routeFootprint_cut_subset_support (C : Set L.Vertex) (p : FinitePath L.web.graph) :
    L.routeFootprint C p ∩ C ⊆ p.support ∩ C := by
  rintro a ⟨ha | ha, haC⟩
  · exact ⟨ha, haC⟩
  · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp ha
    obtain ⟨_hbp, hab⟩ := Set.mem_iUnion.mp hb
    exact (Set.disjoint_left.mp (L.vertexFragmentCarrier_disjoint_cut C b) hab haC).elim

/-- Every good origin record is included in full, including a singleton
record whose carrier has no edge gadgets. -/
theorem recordCarrier_subset_routeFootprint (C : Set L.Vertex) (p : FinitePath L.web.graph)
    (i : I) (hi : i ∉ L.badRecords C) (hpi : p.start = .source i) :
    L.recordCarrier i ⊆ L.routeFootprint C p := by
  classical
  have hs := L.vertexFragmentCarrier_subset_routeFootprint C p (hpi ▸ p.start_mem_support)
  simpa only [vertexFragmentCarrier, if_pos hi] using hs

/-- Every actual fragment touched by a surviving gadget is included,
independently of the representative selected for that gadget. -/
theorem fragmentCarrier_subset_routeFootprint (C : Set L.Vertex) (p : FinitePath L.web.graph)
    {P : L.CutFragment} (hP : P ∈ L.cutFragments C)
    (e : {e : V × V // e ∈ familyEdges L.reference.paths})
    (he : e.1 ∈ P.path.edgeSet) (hep : Vertex.edge e ∈ p.support) :
    L.fragmentCarrier C P ⊆ L.routeFootprint C p := by
  classical
  have heC : e.1 ∉ L.cutEdges C :=
    fun h ↦ Set.disjoint_left.mp (L.cutFragment_edges_disjoint C hP) he h
  have hCarriers := L.fragmentCarrier_eq_of_common C hP (L.edgeFragment_mem C e heC)
    (P.path.edgeSet_subset_support_prod he).1
    ((L.edgeFragment C e heC).path.edgeSet_subset_support_prod (L.edgeFragment_edge C e heC)).1
  have hs := L.vertexFragmentCarrier_subset_routeFootprint C p hep
  simpa only [vertexFragmentCarrier, dif_pos heC, hCarriers] using hs

theorem shortenedRecordFan_footprint_cut_normalized {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
    (r : L.Request S.cut) (hInitial : ∀ i, (L.record i).initial ∉ L.markers)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.shortenedRecordFan S r hInitial).paths) :
    L.routeFootprint S.cut p ∩ S.cut ⊆ {r.1} :=
  (L.routeFootprint_cut_subset_support S.cut p).trans
    (L.shortenedRecordFan_cut_normalized S r hInitial hp)

theorem shortenedRecordFan_other_request_not_footprint {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
    (r s : L.Request S.cut) (hrs : r ≠ s)
    (hInitial : ∀ i, (L.record i).initial ∉ L.markers)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.shortenedRecordFan S r hInitial).paths) :
    s.1 ∉ L.routeFootprint S.cut p := by
  intro hs
  exact hrs (Subtype.ext
    (L.shortenedRecordFan_footprint_cut_normalized S r hInitial hp ⟨hs, s.2.1⟩).symm)

#print axioms routeFootprint_countable
#print axioms recordCarrier_subset_routeFootprint
#print axioms fragmentCarrier_subset_routeFootprint
#print axioms shortenedRecordFan_other_request_not_footprint

end Erdos599.GroundingAllMarkerAuxiliary.Input
