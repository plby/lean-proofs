/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerBlockingPoints
import ErdosProblems.Erdos599.GroundingInitialPrefixOrder

/-!
# Actual stopped fragments for the all-marker grounding construction

Every blocked fragment is replaced by its finite initial prefix through
its unique blocking point. Other fragments, including rays, are retained.
The resulting paths keep all original edges whose tails cannot escape,
and have no outgoing edge at a blocking vertex.
-/

noncomputable section

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

def blockingPrefix (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.blockedFragments C) : FinitePath G.graph :=
  Classical.choose (GroundingPathPrefix.exists_initialFinitePrefix P.path
    (L.fragmentBlockingPoint_mem C hP).1)

theorem blockingPrefix_spec (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.blockedFragments C) :
    (L.blockingPrefix C hP).start = P.path.initial ∧
      (L.blockingPrefix C hP).finish = L.fragmentBlockingPoint C P ∧
      (L.blockingPrefix C hP).support ⊆ P.path.support ∧
      (L.blockingPrefix C hP).edgeSet ⊆ P.path.edgeSet :=
  Classical.choose_spec (GroundingPathPrefix.exists_initialFinitePrefix P.path
    (L.fragmentBlockingPoint_mem C hP).1)

theorem blockingPrefix_mem_edgeSet_iff (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.blockedFragments C) {x y : V} :
    (x, y) ∈ (L.blockingPrefix C hP).edgeSet ↔
      (x, y) ∈ P.path.edgeSet ∧
        GroundingCut.Before P.path x (L.fragmentBlockingPoint C P) := by
  have hspec := L.blockingPrefix_spec C hP
  simpa only [hspec.2.1] using GroundingInitialPrefixOrder.mem_edgeSet_iff_before_finish
    P.path (L.blockingPrefix C hP) hspec.1 hspec.2.2

def stoppedFragment (C : Set L.Vertex) (P : L.CutFragment) : G.DPath := by
  classical
  exact if hP : P ∈ L.blockedFragments C then .inl (L.blockingPrefix C hP) else P.path

theorem stoppedFragment_of_blocked (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.blockedFragments C) :
    L.stoppedFragment C P = .inl (L.blockingPrefix C hP) := by
  classical
  simp only [stoppedFragment, dif_pos hP]

theorem stoppedFragment_of_not_blocked (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∉ L.blockedFragments C) : L.stoppedFragment C P = P.path := by
  classical
  simp only [stoppedFragment, dif_neg hP]

theorem stoppedFragment_initial (C : Set L.Vertex) (P : L.CutFragment) :
    (L.stoppedFragment C P).initial = P.path.initial := by
  classical
  by_cases hP : P ∈ L.blockedFragments C
  · rw [L.stoppedFragment_of_blocked C hP]
    exact (L.blockingPrefix_spec C hP).1
  · rw [L.stoppedFragment_of_not_blocked C hP]

theorem stoppedFragment_support_subset (C : Set L.Vertex) (P : L.CutFragment) :
    (L.stoppedFragment C P).support ⊆ P.path.support := by
  classical
  by_cases hP : P ∈ L.blockedFragments C
  · rw [L.stoppedFragment_of_blocked C hP]
    exact (L.blockingPrefix_spec C hP).2.2.1
  · rw [L.stoppedFragment_of_not_blocked C hP]

theorem stoppedFragment_edgeSet_subset (C : Set L.Vertex) (P : L.CutFragment) :
    (L.stoppedFragment C P).edgeSet ⊆ P.path.edgeSet := by
  classical
  by_cases hP : P ∈ L.blockedFragments C
  · rw [L.stoppedFragment_of_blocked C hP]
    exact (L.blockingPrefix_spec C hP).2.2.2
  · rw [L.stoppedFragment_of_not_blocked C hP]

theorem stoppedFragment_terminal_of_blocked (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.blockedFragments C) :
    (L.stoppedFragment C P).terminal? = some (L.fragmentBlockingPoint C P) := by
  rw [L.stoppedFragment_of_blocked C hP]
  exact congrArg some (L.blockingPrefix_spec C hP).2.1

theorem stoppedFragment_inter_blockingSet (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.blockedFragments C) :
    (L.stoppedFragment C P).support ∩ L.blockingSet C =
      {L.fragmentBlockingPoint C P} := by
  apply Set.Subset.antisymm
  · intro x hx
    exact (L.fragmentBlockingPoint_eq_of_mem C hP.1
      (L.stoppedFragment_support_subset C P hx.1) hx.2).symm
  · rintro x rfl
    refine ⟨?_, (L.fragmentBlockingPoint_mem C hP).2⟩
    rw [L.stoppedFragment_of_blocked C hP]
    exact (L.blockingPrefix_spec C hP).2.1 ▸ (L.blockingPrefix C hP).finish_mem_support

/-- There is no retained original edge with its tail in the separator. -/
theorem stoppedFragment_no_edge_from_blockingSet (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.cutFragments C) {x y : V}
    (he : (x, y) ∈ (L.stoppedFragment C P).edgeSet) : x ∉ L.blockingSet C := by
  intro hxK
  have hxP := P.path.edgeSet_subset_support_prod (L.stoppedFragment_edgeSet_subset C P he)
  have hblocked : P ∈ L.blockedFragments C := ⟨hP, x, hxP.1, hxK⟩
  rw [L.stoppedFragment_of_blocked C hblocked] at he
  have hbefore := (L.blockingPrefix_mem_edgeSet_iff C hblocked).1 he
  exact hbefore.2.2 (L.fragmentBlockingPoint_eq_of_mem C hP hxP.1 hxK).symm

/-- A nonescaping tail is before the blocker, whether the blocker is the
first escape point or the default finite terminal. -/
theorem edge_tail_before_blockingPoint_of_not_escape (C : Set L.Vertex)
    {P : L.CutFragment} (hP : P ∈ L.blockedFragments C) {x y : V}
    (he : (x, y) ∈ P.path.edgeSet) (hxR : x ∉ L.escapeRegion C) :
    GroundingCut.Before P.path x (L.fragmentBlockingPoint C P) := by
  have hxP := (P.path.edgeSet_subset_support_prod he).1
  obtain ⟨hbP, hbK⟩ := L.fragmentBlockingPoint_mem C hP
  rcases hbK with hbOff | hbEscape | hbEnd
  · exact (L.not_mem_cutOff_of_mem_reference C
      ⟨P.parent, P.parent_mem, P.support_subset hbP⟩ hbOff).elim
  · have hnot : ¬ GroundingCut.BeforeEq P.path (L.fragmentBlockingPoint C P) x :=
      fun h ↦ hxR (L.escapeRegion_final_on_cutFragment C hP.1 h hbEscape.2.1)
    refine ⟨(GroundingCut.beforeEq_total hxP hbP).resolve_right hnot, ?_⟩
    intro hxb
    exact hxR (hxb ▸ hbEscape.2.1)
  · have hterminal := L.nonescapingBlocker_terminal C hP.1 hbP hbEnd
    refine ⟨GroundingCut.beforeEq_terminal hterminal hxP, ?_⟩
    intro hxb
    have hfree := hbEnd.2.2.1 y
    exact hfree (hxb ▸ L.residualMatching_of_cutFragment_edge C hP.1 he)

/-- Stopping fragments does not delete any reference edge with a
nonescaping sending port. This also covers unblocked rays. -/
theorem edge_mem_stoppedFragment_of_tail_not_escape (C : Set L.Vertex)
    {P : L.CutFragment} {x y : V}
    (he : (x, y) ∈ P.path.edgeSet) (hxR : x ∉ L.escapeRegion C) :
    (x, y) ∈ (L.stoppedFragment C P).edgeSet := by
  classical
  by_cases hblocked : P ∈ L.blockedFragments C
  · rw [L.stoppedFragment_of_blocked C hblocked]
    exact (L.blockingPrefix_mem_edgeSet_iff C hblocked).2
      ⟨he, L.edge_tail_before_blockingPoint_of_not_escape C hblocked he hxR⟩
  · rw [L.stoppedFragment_of_not_blocked C hblocked]
    exact he

#print axioms blockingPrefix_mem_edgeSet_iff
#print axioms stoppedFragment_inter_blockingSet
#print axioms stoppedFragment_no_edge_from_blockingSet
#print axioms edge_mem_stoppedFragment_of_tail_not_escape

end Erdos599.GroundingAllMarkerAuxiliary.Input
