/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerFragmentTracks

/-!
# Stationary request fans avoiding every hanging cut fragment

The concrete first-contact pruning removes attachable fragment contacts.
Uncut-marker fragment contacts were already impossible by auxiliary
separation. Every remaining internal reference gadget therefore belongs
to a fragment whose own initial is an original source vertex.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set Cardinal DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I) {kappa : Cardinal.{u}}

def prunedRecordFan {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut) :
    Popular.JoinedFamily L.web {r.1} :=
  (L.fragmentTracks S.cut).avoidingFan (L.goodRecordFan S r)

theorem prunedRecordFan_subset_good {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut) :
    (L.prunedRecordFan S r).paths ⊆ (L.goodRecordFan S r).paths := fun _ hp ↦ hp.1

theorem prunedRecordFan_stationary {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut) :
    Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf U (L.prunedRecordFan S r).paths
        (L.prunedRecordFan S r).starts_in_source) :=
  (L.fragmentTracks S.cut).avoidingFan_stationary U r.2.1 (L.goodRecordFan S r)
    (L.goodRecordFan_cut_normalized S r) S.not_strongly_popular
    (L.goodRecordFan_stationary S r)

theorem prunedRecordFan_cut_normalized {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.prunedRecordFan S r).paths) :
    p.support ∩ S.cut ⊆ {r.1} :=
  L.goodRecordFan_cut_normalized S r (L.prunedRecordFan_subset_good S r hp)

theorem prunedRecordFan_start_good_record {U : Popular.KappaIndexed L.web kappa}
    (S : Popular.PopularSeparator U) (r : L.Request S.cut)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.prunedRecordFan S r).paths) :
    ∃ i : I, p.start = Vertex.source i ∧ i ∉ L.badRecords S.cut :=
  L.goodRecordFan_start_good_record S r (L.prunedRecordFan_subset_good S r hp)

theorem prunedRecordFan_avoids_attachable_fragment
    {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
    (r : L.Request S.cut) {p : FinitePath L.web.graph}
    (hp : p ∈ (L.prunedRecordFan S r).paths) {P : L.CutFragment}
    (hP : P ∈ L.cutFragments S.cut) (hAttach : L.CutFragmentAttachable S.cut P) :
    Disjoint p.support (L.fragmentEdgeVertices P) :=
  Set.disjoint_left.mpr (fun _ hap haP ↦ Set.disjoint_left.mp
    ((L.fragmentTracks S.cut).avoidingFan_disjoint_tracks (L.goodRecordFan S r) hp)
    hap (L.fragmentEdgeVertices_subset_tracks S.cut hP hAttach haP))

/-- This excludes every hanging fragment, not just those meeting the
blocking set. The grounded condition is on the actual fragment initial. -/
theorem prunedRecordFan_avoids_hanging_fragment
    {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
    (r : L.Request S.cut)
    (hInitials : G.initialSet L.reference.paths ⊆ G.source ∪ L.markers)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.prunedRecordFan S r).paths)
    {P : L.CutFragment} (hP : P ∈ L.cutFragments S.cut)
    (hHang : ¬ L.CutFragmentGrounded P) :
    Disjoint p.support (L.fragmentEdgeVertices P) := by
  rcases L.cutFragment_initial_eq_parent_or_cutHead S.cut hP with hfirst | hcut
  · have hinit : P.path.initial ∈ G.source ∪ L.markers :=
      hfirst ▸ hInitials ⟨P.parent, P.parent_mem, rfl⟩
    have hmarker : P.path.initial ∈ L.markers := hinit.resolve_left hHang
    let y : L.markers := ⟨P.path.initial, hmarker⟩
    by_cases hy : Vertex.marker y ∈ S.cut
    · exact L.prunedRecordFan_avoids_attachable_fragment S r hp hP
        (Or.inl ⟨y, hy, rfl⟩)
    · exact L.goodRecordFan_avoids_uncut_marker_fragment S r
        (L.prunedRecordFan_subset_good S r hp) hP y hy rfl
  · exact L.prunedRecordFan_avoids_attachable_fragment S r hp hP (Or.inr hcut)

theorem prunedRecordFan_contact_fragment_grounded
    {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
    (r : L.Request S.cut)
    (hInitials : G.initialSet L.reference.paths ⊆ G.source ∪ L.markers)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.prunedRecordFan S r).paths)
    {P : L.CutFragment} (hP : P ∈ L.cutFragments S.cut)
    {a : L.Vertex} (hap : a ∈ p.support) (haP : a ∈ L.fragmentEdgeVertices P) :
    L.CutFragmentGrounded P := by
  classical
  by_contra hHang
  exact Set.disjoint_left.mp
    (L.prunedRecordFan_avoids_hanging_fragment S r hInitials hp hP hHang) hap haP

/-- Every internal edge gadget is covered by an actual grounded surviving
fragment. The cut endpoint itself is deliberately excluded. -/
theorem prunedRecordFan_internal_edge_grounded
    {U : Popular.KappaIndexed L.web kappa} (S : Popular.PopularSeparator U)
    (r : L.Request S.cut)
    (hInitials : G.initialSet L.reference.paths ⊆ G.source ∪ L.markers)
    {p : FinitePath L.web.graph} (hp : p ∈ (L.prunedRecordFan S r).paths)
    (e : {e : V × V // e ∈ familyEdges L.reference.paths})
    (he : Vertex.edge e ∈ p.support) (her : Vertex.edge e ≠ r.1) :
    ∃ P : L.CutFragment, P ∈ L.cutFragments S.cut ∧
      L.CutFragmentGrounded P ∧ e.1 ∈ P.path.edgeSet := by
  have heNotCut : e.1 ∉ L.cutEdges S.cut := by
    rintro ⟨heRef, heC⟩
    exact her (L.prunedRecordFan_cut_normalized S r hp ⟨he, heC⟩)
  obtain ⟨P, hP, heP⟩ := L.exists_cutFragment_containing_edge S.cut e.2 heNotCut
  exact ⟨P, hP, L.prunedRecordFan_contact_fragment_grounded S r hInitials hp hP he heP, heP⟩

#print axioms prunedRecordFan_stationary
#print axioms prunedRecordFan_avoids_hanging_fragment
#print axioms prunedRecordFan_internal_edge_grounded

end Erdos599.GroundingAllMarkerAuxiliary.Input
