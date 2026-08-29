/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerFragments

/-!
# The escape region is a final interval on each actual cut fragment

On the reference warp every identity is a forward residual edge. An uncut
reference edge can therefore be traversed backwards between sending ports
using an identity followed by its reversed matching edge. This transports
escape membership forwards along the original fragment. In particular a
fragment starting at an uncut marker lies wholly in the escape region.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

theorem escapes_of_walk_to (C : Set L.Vertex) {p q : Port V}
    (w : Walk (L.residualGraph C) p q) (hq : L.Escapes C q) : L.Escapes C p := by
  obtain ⟨y, hy, ⟨v⟩⟩ := hq
  exact ⟨y, hy, ⟨w.append v⟩⟩

theorem residualStep_identity_of_mem_reference (C : Set L.Vertex) {x : V}
    (hx : x ∈ G.vertexSet L.reference.paths) : L.residualStep C (.inl x) (.inr x) := by
  have hxC := L.not_mem_cutOff_of_mem_reference C hx
  refine ⟨hxC, hxC, Or.inr rfl, ?_⟩
  rintro (⟨he, _⟩ | ⟨_, hoff⟩)
  · simp only [familyEdges, Set.mem_iUnion] at he
    obtain ⟨P, _hP, heP⟩ := he
    exact GroundingFragmentResidualOrder.ne_of_mem_dpath_edgeSet heP rfl
  · exact hoff hx

theorem escapeRegion_mono_surviving_edge (C : Set L.Vertex) {x y : V}
    (he : (x, y) ∈ familyEdges L.reference.paths) (hnot : (x, y) ∉ L.cutEdges C)
    (hx : x ∈ L.escapeRegion C) : y ∈ L.escapeRegion C := by
  have hxy := familyEdges_subset_vertexSet_prod L.reference.paths he
  have hid : (L.residualGraph C).Adj (.inl y) (.inr y) :=
    L.residualStep_identity_of_mem_reference C hxy.2
  have hback : (L.residualGraph C).Adj (.inr y) (.inl x) :=
    ⟨L.not_mem_cutOff_of_mem_reference C hxy.2,
      L.not_mem_cutOff_of_mem_reference C hxy.1, Or.inl ⟨he, hnot⟩⟩
  exact L.escapes_of_walk_to C (.cons hid (.cons hback .nil)) hx

theorem escapeRegion_mono_surviving_walk (C : Set L.Vertex) {x y : V}
    (w : Walk G.graph x y) (hEdges : w.edgeSet ⊆ familyEdges L.reference.paths)
    (hCut : Disjoint w.edgeSet (L.cutEdges C))
    (hx : x ∈ L.escapeRegion C) : y ∈ L.escapeRegion C := by
  induction w with
  | nil => exact hx
  | @cons x z y e w ih =>
      have hz : z ∈ L.escapeRegion C := L.escapeRegion_mono_surviving_edge C
        (hEdges (Or.inl rfl))
        (Set.disjoint_left.mp hCut (Or.inl rfl)) hx
      apply ih (fun _ he ↦ hEdges (Or.inr he)) ?_ hz
      exact Set.disjoint_left.mpr (fun _ he ↦ Set.disjoint_left.mp hCut (Or.inr he))

/-- Only the fragment's genuine forward interval is used; ambient chords
are not silently substituted for retained reference edges. -/
theorem escapeRegion_final_on_cutFragment (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.cutFragments C) {x y : V} (hxy : GroundingCut.BeforeEq P.path x y)
    (hx : x ∈ L.escapeRegion C) : y ∈ L.escapeRegion C := by
  by_cases hEq : x = y
  · exact hEq ▸ hx
  obtain ⟨p, hpStart, hpFinish, hpEdges⟩ :=
    GroundingCutDecoder.exists_forward_segment_of_before ⟨hxy, hEq⟩
  have hEdges : p.walk.edgeSet ⊆ familyEdges L.reference.paths := by
    intro e he
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨P.parent, P.parent_mem, P.edges_subset (hpEdges he)⟩
  have hCut : Disjoint p.walk.edgeSet (L.cutEdges C) :=
    Set.disjoint_left.mpr (fun _ he ↦
      Set.disjoint_left.mp (L.cutFragment_edges_disjoint C hP) (hpEdges he))
  have hx' : p.start ∈ L.escapeRegion C := hpStart ▸ hx
  exact hpFinish ▸ L.escapeRegion_mono_surviving_walk C p.walk hEdges hCut hx'

/-- The marker's identity is unmatched even when its owner is an isolated
reference component. It gives the initial escape without an outgoing edge. -/
theorem marker_mem_escapeRegion (C : Set L.Vertex) (y : L.markers)
    (hy : Vertex.marker y ∉ C) : y.1 ∈ L.escapeRegion C := by
  have hyY : y.1 ∈ G.vertexSet L.reference.paths := by
    obtain ⟨p, hp, hpy⟩ := L.markers_initial y.2
    exact ⟨p, hp, hpy ▸ p.initial_mem_support⟩
  have hid : (L.residualGraph C).Adj (.inl y.1) (.inr y.1) :=
    L.residualStep_identity_of_mem_reference C hyY
  exact ⟨y, hy, ⟨.cons hid .nil⟩⟩

theorem cutFragment_subset_escapeRegion_of_uncut_marker_initial
    (C : Set L.Vertex) {P : L.CutFragment} (hP : P ∈ L.cutFragments C)
    (y : L.markers) (hy : Vertex.marker y ∉ C) (hinitial : P.path.initial = y.1) :
    P.path.support ⊆ L.escapeRegion C := by
  intro x hx
  apply L.escapeRegion_final_on_cutFragment C hP
    (GroundingFragmentWarp.initial_beforeEq_of_mem hx)
  exact hinitial ▸ L.marker_mem_escapeRegion C y hy

#print axioms escapeRegion_final_on_cutFragment
#print axioms marker_mem_escapeRegion
#print axioms cutFragment_subset_escapeRegion_of_uncut_marker_initial

end Erdos599.GroundingAllMarkerAuxiliary.Input
