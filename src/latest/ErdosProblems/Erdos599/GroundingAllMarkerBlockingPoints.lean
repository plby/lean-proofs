/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerBlockingSet

/-!
# The separating set has exactly one point on each blocked fragment

An escaping blocker is the first escape vertex of its fragment; a
nonescaping blocker is its finite terminal and its fragment misses the
escape region. These facts identify the vertexwise separator with the
prescribed fragment blocking points, without conflating fragment initials
with their parent initials or discarding singleton and ray fragments.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

theorem residualMatching_of_cutFragment_edge (C : Set L.Vertex)
    {P : L.CutFragment} (hP : P ∈ L.cutFragments C) {x y : V}
    (he : (x, y) ∈ P.path.edgeSet) : L.residualMatching C x y := by
  refine Or.inl ⟨?_, Set.disjoint_left.mp (L.cutFragment_edges_disjoint C hP) he⟩
  simp only [familyEdges, Set.mem_iUnion]
  exact ⟨P.parent, P.parent_mem, P.edges_subset he⟩

private theorem escapeRegion_on_surviving_walk (C : Set L.Vertex) {x y : V}
    (w : Walk G.graph x y) (hEdges : w.edgeSet ⊆ familyEdges L.reference.paths)
    (hCut : Disjoint w.edgeSet (L.cutEdges C)) (hx : x ∈ L.escapeRegion C) :
    ∀ z ∈ w.support, z ∈ L.escapeRegion C := by
  induction w with
  | nil =>
      intro z hz
      simp only [Walk.support_nil, List.mem_singleton] at hz
      subst z
      exact hx
  | @cons x t y e w ih =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx
      · have ht : t ∈ L.escapeRegion C := L.escapeRegion_mono_surviving_edge C
          (hEdges (Or.inl rfl)) (Set.disjoint_left.mp hCut (Or.inl rfl)) hx
        exact ih (fun _ he ↦ hEdges (Or.inr he))
          (Set.disjoint_left.mpr (fun _ he ↦ Set.disjoint_left.mp hCut (Or.inr he))) ht z hz

theorem escaping_predecessor_of_before (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.cutFragments C) {x y : V} (hxy : GroundingCut.Before P.path x y)
    (hx : x ∈ L.escapeRegion C) :
    ∃ z, L.residualMatching C z y ∧ z ∈ L.escapeRegion C := by
  obtain ⟨q, hqx, hqy, hEdges⟩ := GroundingCutDecoder.exists_forward_segment_of_before hxy
  have hne : q.finish ≠ q.start := by
    rw [hqx, hqy]
    exact hxy.2.symm
  obtain ⟨z, hz⟩ := FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
    q q.finish_mem_support hne
  have hFamily : q.walk.edgeSet ⊆ familyEdges L.reference.paths := by
    intro e he
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨P.parent, P.parent_mem, P.edges_subset (hEdges he)⟩
  have hCut : Disjoint q.walk.edgeSet (L.cutEdges C) :=
    Set.disjoint_left.mpr (fun _ he ↦
      Set.disjoint_left.mp (L.cutFragment_edges_disjoint C hP) (hEdges he))
  refine ⟨z, hqy ▸ L.residualMatching_of_cutFragment_edge C hP (hEdges hz), ?_⟩
  exact L.escapeRegion_on_surviving_walk C q.walk hFamily hCut (hqx ▸ hx) z
    (q.edgeSet_subset_support_prod hz).1

theorem firstVertex_eq_escapingBlocker (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.cutFragments C) (hR : (P.path.support ∩ L.escapeRegion C).Nonempty)
    {x : V} (hxP : x ∈ P.path.support) (hx : x ∈ L.escapingBlockers C) :
    GroundingCut.firstVertex P.path (L.escapeRegion C) hR = x := by
  by_contra hne
  exact hx.2.2.2 (L.escaping_predecessor_of_before C hP
    ⟨GroundingCut.firstVertex_beforeEq P.path (L.escapeRegion C) hR ⟨hxP, hx.2.1⟩, hne⟩
    (GroundingCut.firstVertex_mem P.path (L.escapeRegion C) hR).2)

theorem nonescapingBlocker_terminal (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.cutFragments C) {x : V} (hxP : x ∈ P.path.support)
    (hx : x ∈ L.nonescapingBlockers C) : P.path.terminal? = some x := by
  cases hPath : P.path with
  | inl f =>
      by_cases hfinish : f.finish = x
      · simp only [Path.terminal?, hfinish]
      · have hxF : x ∈ f.support := by simpa only [hPath, Path.support] using hxP
        obtain ⟨y, hxy⟩ := FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
          f hxF (fun h ↦ hfinish h.symm)
        exact (hx.2.2.1 y (L.residualMatching_of_cutFragment_edge C hP
          (by simpa only [hPath, Path.edgeSet] using hxy))).elim
  | inr r =>
      have hxR : x ∈ r.support := by simpa only [hPath, Path.support] using hxP
      obtain ⟨n, rfl⟩ := hxR
      have he : (r n, r (n + 1)) ∈ P.path.edgeSet := by
        rw [hPath]
        exact ⟨n, rfl⟩
      exact (hx.2.2.1 (r (n + 1)) (L.residualMatching_of_cutFragment_edge C hP he)).elim

theorem nonescapingBlocker_fragment_misses_escape (C : Set L.Vertex)
    {P : L.CutFragment} (hP : P ∈ L.cutFragments C) {x : V}
    (hxP : x ∈ P.path.support) (hx : x ∈ L.nonescapingBlockers C) :
    Disjoint P.path.support (L.escapeRegion C) := by
  apply Set.disjoint_left.mpr
  intro y hyP hyR
  exact hx.2.1 (L.escapeRegion_final_on_cutFragment C hP
    (GroundingCut.beforeEq_terminal (L.nonescapingBlocker_terminal C hP hxP hx) hyP) hyR)

def fragmentBlockingPoint (C : Set L.Vertex) (P : L.CutFragment) : V := by
  classical
  exact if hR : (P.path.support ∩ L.escapeRegion C).Nonempty then
    GroundingCut.firstVertex P.path (L.escapeRegion C) hR
  else P.path.terminal?.getD P.path.initial

/-- The vertexwise definition selects the literal first escape point or
finite terminal, not just some point on the same parent component. -/
theorem fragmentBlockingPoint_eq_of_mem (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.cutFragments C) {x : V} (hxP : x ∈ P.path.support)
    (hxK : x ∈ L.blockingSet C) : L.fragmentBlockingPoint C P = x := by
  rcases hxK with hxOff | hxEscape | hxEnd
  · exact (L.not_mem_cutOff_of_mem_reference C
      ⟨P.parent, P.parent_mem, P.support_subset hxP⟩ hxOff).elim
  · have hR : (P.path.support ∩ L.escapeRegion C).Nonempty := ⟨x, hxP, hxEscape.2.1⟩
    rw [fragmentBlockingPoint, dif_pos hR]
    exact L.firstVertex_eq_escapingBlocker C hP hR hxP hxEscape
  · have hR : ¬ (P.path.support ∩ L.escapeRegion C).Nonempty := by
      rintro ⟨y, hyP, hyR⟩
      exact Set.disjoint_left.mp
        (L.nonescapingBlocker_fragment_misses_escape C hP hxP hxEnd) hyP hyR
    simp only [fragmentBlockingPoint, dif_neg hR,
      L.nonescapingBlocker_terminal C hP hxP hxEnd, Option.getD_some]

theorem cutFragment_blockingSet_subsingleton (C : Set L.Vertex)
    {P : L.CutFragment} (hP : P ∈ L.cutFragments C) :
    (P.path.support ∩ L.blockingSet C).Subsingleton := by
  intro x hx y hy
  exact (L.fragmentBlockingPoint_eq_of_mem C hP hx.1 hx.2).symm.trans
    (L.fragmentBlockingPoint_eq_of_mem C hP hy.1 hy.2)

def blockedFragments (C : Set L.Vertex) : Set L.CutFragment :=
  {P | P ∈ L.cutFragments C ∧ (P.path.support ∩ L.blockingSet C).Nonempty}

theorem blockedFragment_meets_escape_or_finite (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.blockedFragments C) :
    (P.path.support ∩ L.escapeRegion C).Nonempty ∨ P.path.IsFinite := by
  obtain ⟨x, hxP, hxOff | hxEscape | hxEnd⟩ := hP.2
  · exact (L.not_mem_cutOff_of_mem_reference C
      ⟨P.parent, P.parent_mem, P.support_subset hxP⟩ hxOff).elim
  · exact Or.inl ⟨x, hxP, hxEscape.2.1⟩
  · exact Or.inr ⟨x, L.nonescapingBlocker_terminal C hP.1 hxP hxEnd⟩

theorem fragmentBlockingPoint_beforeEq_escape (C : Set L.Vertex) {P : L.CutFragment}
    {x : V} (hxP : x ∈ P.path.support) (hxR : x ∈ L.escapeRegion C) :
    GroundingCut.BeforeEq P.path (L.fragmentBlockingPoint C P) x := by
  have hR : (P.path.support ∩ L.escapeRegion C).Nonempty := ⟨x, hxP, hxR⟩
  rw [fragmentBlockingPoint, dif_pos hR]
  exact GroundingCut.firstVertex_beforeEq P.path (L.escapeRegion C) hR ⟨hxP, hxR⟩

theorem fragmentBlockingPoint_mem (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.blockedFragments C) :
    L.fragmentBlockingPoint C P ∈ P.path.support ∩ L.blockingSet C := by
  obtain ⟨x, hxP, hxK⟩ := hP.2
  rw [L.fragmentBlockingPoint_eq_of_mem C hP.1 hxP hxK]
  exact ⟨hxP, hxK⟩

theorem cutFragment_inter_blockingSet_eq_singleton (C : Set L.Vertex)
    {P : L.CutFragment} (hP : P ∈ L.blockedFragments C) :
    P.path.support ∩ L.blockingSet C = {L.fragmentBlockingPoint C P} := by
  ext x
  constructor
  · intro hx
    exact (L.fragmentBlockingPoint_eq_of_mem C hP.1 hx.1 hx.2).symm
  · rintro rfl
    exact L.fragmentBlockingPoint_mem C hP

/-- Exact coverage of the vertexwise separator by the off-reference cut
and the actual singleton blocking points of maximal surviving fragments. -/
theorem blockingSet_eq_cutOff_union_fragmentBlockingPoints (C : Set L.Vertex) :
    L.blockingSet C = L.cutOffVertices C ∪
      L.fragmentBlockingPoint C '' L.blockedFragments C := by
  ext x
  constructor
  · intro hx
    by_cases hxOff : x ∈ L.cutOffVertices C
    · exact Or.inl hxOff
    · have hxY : x ∈ G.vertexSet L.reference.paths := by
        rcases hx with h | h | h
        · exact (hxOff h).elim
        · exact h.1
        · exact h.1
      obtain ⟨p, hp, hxp⟩ := hxY
      obtain ⟨P, _hparent, hP, hxP⟩ := L.exists_cutFragment_containing C hp hxp
      exact Or.inr ⟨P, ⟨hP, x, hxP, hx⟩, L.fragmentBlockingPoint_eq_of_mem C hP hxP hx⟩
  · rintro (hx | ⟨P, hP, rfl⟩)
    · exact Or.inl hx
    · exact (L.fragmentBlockingPoint_mem C hP).2

#print axioms firstVertex_eq_escapingBlocker
#print axioms nonescapingBlocker_terminal
#print axioms cutFragment_inter_blockingSet_eq_singleton
#print axioms blockingSet_eq_cutOff_union_fragmentBlockingPoints

end Erdos599.GroundingAllMarkerAuxiliary.Input
