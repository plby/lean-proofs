/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerEscapeOrder
import ErdosProblems.Erdos599.GroundingAllMarkerRecordAvoidance

/-!
# The vertexwise blocking set and its separating property

The escaping boundary consists of reference vertices with no escaping
matched predecessor, except uncut markers. The nonescaping part consists
of free reference sending endpoints outside the good record owners.
Together with the off-reference cut these are the fragment blocking points
of the mathematical writeup. This file proves separation directly by
backwards propagation along finite original walks. The source and terminal
profiles remain explicit so that the actual ladder must discharge them.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

def uncutMarkerVertices (C : Set L.Vertex) : Set V :=
  {x | ∃ y : L.markers, y.1 = x ∧ Vertex.marker y ∉ C}

def goodRecordVertices (C : Set L.Vertex) : Set V :=
  {x | ∃ i : I, i ∉ L.badRecords C ∧ x ∈ (L.record i).support}

def escapingBlockers (C : Set L.Vertex) : Set V :=
  {x | x ∈ G.vertexSet L.reference.paths ∧ x ∈ L.escapeRegion C ∧
    x ∉ L.uncutMarkerVertices C ∧
    ¬ ∃ z, L.residualMatching C z x ∧ z ∈ L.escapeRegion C}

def nonescapingBlockers (C : Set L.Vertex) : Set V :=
  {x | x ∈ G.vertexSet L.reference.paths ∧ x ∉ L.escapeRegion C ∧
    (∀ z, ¬ L.residualMatching C x z) ∧ x ∉ L.goodRecordVertices C}

def blockingSet (C : Set L.Vertex) : Set V :=
  L.cutOffVertices C ∪ (L.escapingBlockers C ∪ L.nonescapingBlockers C)

theorem not_mem_cutOff_of_not_mem_blockingSet (C : Set L.Vertex) {x : V}
    (hx : x ∉ L.blockingSet C) : x ∉ L.cutOffVertices C :=
  fun h ↦ hx (Or.inl h)

theorem initial_mem_reference {x : V} (hx : x ∈ G.initialSet L.reference.paths) :
    x ∈ G.vertexSet L.reference.paths := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨p, hp, p.initial_mem_support⟩

theorem residualMatching_noIncoming_initial (C : Set L.Vertex) {x : V}
    (hx : x ∈ G.initialSet L.reference.paths) (z : V) :
    ¬ L.residualMatching C z x := by
  intro h
  rcases L.residualMatching_subset_reference C h with he | ⟨rfl, hoff⟩
  · exact Blueprint.LinkageBlueprint.isWarp_noIncoming_familyEdges_of_mem_initialSet
      L.reference.disjoint hx ⟨z, he⟩
  · exact hoff (L.initial_mem_reference hx)

theorem residualMatching_noOutgoing_terminal (C : Set L.Vertex) {x : V}
    (hx : x ∈ G.terminalFrontier L.reference.paths) (z : V) :
    ¬ L.residualMatching C x z := by
  intro h
  rcases L.residualMatching_subset_reference C h with he | ⟨_, hoff⟩
  · exact Blueprint.LinkageBlueprint.isWarp_noOutgoing_familyEdges_of_mem_terminalFrontier
      L.reference.disjoint hx ⟨z, he⟩
  · obtain ⟨p, hp, ht⟩ := hx
    exact hoff ⟨p, hp, G.terminal_mem_support ht⟩

/-- A matching predecessor transfers escape backwards across an original
edge. If that edge itself is matched, its tail is that predecessor. -/
theorem escapeRegion_of_adj_of_matching_predecessor (C : Set L.Vertex)
    {x y z : V} (hxy : G.graph.Adj x y) (hxC : x ∉ L.cutOffVertices C)
    (hyC : y ∉ L.cutOffVertices C) (hzC : z ∉ L.cutOffVertices C)
    (hzy : L.residualMatching C z y) (hz : z ∈ L.escapeRegion C) :
    x ∈ L.escapeRegion C := by
  by_cases hxz : x = z
  · exact hxz ▸ hz
  have hforward : (L.residualGraph C).Adj (.inl x) (.inr y) := by
    refine ⟨hxC, hyC, Or.inl hxy, ?_⟩
    intro hmatch
    exact hxz ((referenceMatching_biUnique L.reference.disjoint).1
      (L.residualMatching_subset_reference C hmatch)
      (L.residualMatching_subset_reference C hzy))
  have hback : (L.residualGraph C).Adj (.inr y) (.inl z) := ⟨hyC, hzC, hzy⟩
  exact L.escapes_of_walk_to C (.cons hforward (.cons hback .nil)) hz

theorem escapeRegion_of_adj_to_uncutMarker (C : Set L.Vertex)
    {x : V} (y : L.markers) (hy : Vertex.marker y ∉ C)
    (hxy : G.graph.Adj x y.1) (hxC : x ∉ L.cutOffVertices C) :
    x ∈ L.escapeRegion C := by
  have hyC := L.not_mem_cutOff_of_mem_reference C
    (L.initial_mem_reference (L.markers_initial y.2))
  have he : (L.residualGraph C).Adj (.inl x) (.inr y.1) := by
    refine ⟨hxC, hyC, Or.inl hxy, ?_⟩
    exact L.residualMatching_noIncoming_initial C (L.markers_initial y.2) x
  exact ⟨y, hy, ⟨.cons he .nil⟩⟩

/-- Avoiding the blocking set makes the escape region backward closed
under original graph edges. No assumption about a chosen path is used. -/
theorem blockingSet_backward_closed (C : Set L.Vertex) {x y : V}
    (hxy : G.graph.Adj x y) (hxK : x ∉ L.blockingSet C)
    (hyK : y ∉ L.blockingSet C) (hyR : y ∈ L.escapeRegion C) :
    x ∈ L.escapeRegion C := by
  have hxC := L.not_mem_cutOff_of_not_mem_blockingSet C hxK
  have hyC := L.not_mem_cutOff_of_not_mem_blockingSet C hyK
  by_cases hyY : y ∈ G.vertexSet L.reference.paths
  · by_cases hpred : ∃ z, L.residualMatching C z y ∧ z ∈ L.escapeRegion C
    · obtain ⟨z, hzy, hzR⟩ := hpred
      have hzY : z ∈ G.vertexSet L.reference.paths := by
        rcases hzy with ⟨he, _⟩ | ⟨rfl, hoff⟩
        · exact (familyEdges_subset_vertexSet_prod L.reference.paths he).1
        · exact (hoff hyY).elim
      exact L.escapeRegion_of_adj_of_matching_predecessor C hxy hxC hyC
        (L.not_mem_cutOff_of_mem_reference C hzY) hzy hzR
    · have hyM : y ∈ L.uncutMarkerVertices C := by
        by_contra hyM
        exact hyK (Or.inr (Or.inl ⟨hyY, hyR, hyM, hpred⟩))
      obtain ⟨m, rfl, hm⟩ := hyM
      exact L.escapeRegion_of_adj_to_uncutMarker C m hm hxy hxC
  · exact L.escapeRegion_of_adj_of_matching_predecessor C hxy hxC hyC hyC
      (Or.inr ⟨rfl, hyY⟩) hyR

theorem blockingSet_backward_closed_walk (C : Set L.Vertex) {x y : V}
    (w : Walk G.graph x y) (hw : ∀ z ∈ w.support, z ∉ L.blockingSet C)
    (hy : y ∈ L.escapeRegion C) : x ∈ L.escapeRegion C := by
  induction w with
  | nil => exact hy
  | @cons x z y hxy w ih =>
      have hz := ih (fun v hv ↦ hw v (List.mem_cons_of_mem _ hv)) hy
      exact L.blockingSet_backward_closed C hxy
        (hw x (List.mem_cons_self))
        (hw z (List.mem_cons_of_mem _ w.start_mem_support)) hz

theorem source_not_escape_of_not_blockingSet (C : Set L.Vertex)
    (hsource : G.source ⊆ G.initialSet L.reference.paths)
    (hdisjoint : Disjoint G.source L.markers) {x : V} (hx : x ∈ G.source)
    (hxK : x ∉ L.blockingSet C) : x ∉ L.escapeRegion C := by
  intro hxR
  apply hxK
  refine Or.inr (Or.inl ⟨L.initial_mem_reference (hsource hx), hxR, ?_, ?_⟩)
  · rintro ⟨y, rfl, _⟩
    exact Set.disjoint_left.mp hdisjoint hx y.2
  · rintro ⟨z, hzx, _⟩
    exact L.residualMatching_noIncoming_initial C (hsource hx) z hzx

theorem terminal_escape_of_not_blockingSet (C : Set L.Vertex) {x : V}
    (hx : x ∈ G.terminalFrontier L.reference.paths)
    (hxGood : x ∉ L.goodRecordVertices C) (hxK : x ∉ L.blockingSet C) :
    x ∈ L.escapeRegion C := by
  by_contra hxR
  have hxY : x ∈ G.vertexSet L.reference.paths := by
    obtain ⟨p, hp, ht⟩ := hx
    exact ⟨p, hp, G.terminal_mem_support ht⟩
  exact hxK (Or.inr (Or.inr
    ⟨hxY, hxR, L.residualMatching_noOutgoing_terminal C hx, hxGood⟩))

theorem blockingSet_hits_source_terminal_walk (C : Set L.Vertex)
    (hsource : G.source ⊆ G.initialSet L.reference.paths)
    (hdisjoint : Disjoint G.source L.markers) {x y : V}
    (w : Walk G.graph x y) (hx : x ∈ G.source)
    (hy : y ∈ G.terminalFrontier L.reference.paths)
    (hyGood : y ∉ L.goodRecordVertices C) :
    ∃ z ∈ w.support, z ∈ L.blockingSet C := by
  by_contra hnone
  have hav : ∀ z ∈ w.support, z ∉ L.blockingSet C := by
    intro z hz hzK
    exact hnone ⟨z, hz, hzK⟩
  have hyR := L.terminal_escape_of_not_blockingSet C hy hyGood (hav y w.end_mem_support)
  exact L.source_not_escape_of_not_blockingSet C hsource hdisjoint hx
    (hav x w.start_mem_support) (L.blockingSet_backward_closed_walk C w hav hyR)

/-- A genuinely separating terminal frontier yields a genuinely separating
blocking set. The good-record exclusion is required only at that frontier. -/
theorem blockingSet_separates (C : Set L.Vertex)
    (hsource : G.source ⊆ G.initialSet L.reference.paths)
    (hdisjoint : Disjoint G.source L.markers) (T : Set V)
    (hT : Popular.IsSeparator G T) (hterminal : T ⊆ G.terminalFrontier L.reference.paths)
    (hgood : Disjoint T (L.goodRecordVertices C)) : Popular.IsSeparator G (L.blockingSet C) := by
  intro p hpA hpB
  obtain ⟨t, htp, htT⟩ := hT p hpA hpB
  have hmeet : p.walk.Meets T := ⟨t, htp, htT⟩
  let q := p.firstHit T hmeet
  have hqT : q.finish ∈ T := p.firstHit_finish_mem T hmeet
  obtain ⟨z, hzq, hzK⟩ := L.blockingSet_hits_source_terminal_walk C hsource hdisjoint q.walk
    hpA (hterminal hqT) (Set.disjoint_left.mp hgood hqT)
  exact ⟨z, p.firstHit_support_subset T hmeet hzq, hzK⟩

/-- Separation in the auxiliary ensures that no blocking point is placed
on any good original record, including a ray or an isolated record. -/
theorem goodRecordVertices_disjoint_blockingSet (C : Set L.Vertex)
    (hC : Popular.IsSeparator L.web C) :
    Disjoint (L.goodRecordVertices C) (L.blockingSet C) := by
  apply Set.disjoint_left.mpr
  rintro x hxGood (hxOff | hxEscape | hxEnd)
  · obtain ⟨i, _hi, hxi⟩ := hxGood
    exact L.not_mem_cutOff_of_mem_reference C ⟨L.record i, L.record_mem i, hxi⟩ hxOff
  · obtain ⟨i, hi, hxi⟩ := hxGood
    exact L.not_escapes_of_mem_uncut_record C hC hi hxi hxEscape.2.1
  · exact hxEnd.2.2.2 hxGood

#print axioms blockingSet_backward_closed
#print axioms blockingSet_hits_source_terminal_walk
#print axioms blockingSet_separates
#print axioms goodRecordVertices_disjoint_blockingSet

end Erdos599.GroundingAllMarkerAuxiliary.Input
