/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAllMarkerShortenedFans

/-!
# Cut-avoiding countable fragment carriers

A fragment carrier includes its surviving edge gadgets and its parent's
source tag only when that parent is a good record. Such a good record is
an entire uncut fragment. Thus these added tags do not join different
fragments of a cut owner, and all carrier vertices avoid the cut.
-/

namespace Erdos599.GroundingAllMarkerAuxiliary.Input

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V I : Type u} {G : DWeb V} (L : Input G I)

def recordFragment (i : I) : L.CutFragment where
  path := L.record i
  parent := L.record i
  parent_mem := L.record_mem i
  support_subset := Set.Subset.rfl
  edges_subset := Set.Subset.rfl

theorem recordCarrier_countable (i : I) : (L.recordCarrier i).Countable := by
  apply ((Set.countable_singleton (Vertex.source i)).union
    (L.fragmentEdgeVertices_countable (L.recordFragment i))).mono
  intro a ha
  cases a with
  | source j => exact Or.inl (congrArg Vertex.source ha)
  | edge e => exact Or.inr ha
  | marker y => exact ha.elim
  | off x => exact ha.elim

theorem recordFragment_mem (C : Set L.Vertex) (i : I) (hi : i ∉ L.badRecords C) :
    L.recordFragment i ∈ L.cutFragments C := by
  have hEdges : Disjoint (L.record i).edgeSet (L.cutEdges C) :=
    Set.disjoint_left.mpr (fun e he heC ↦ hi (Or.inr ⟨e, he, heC⟩))
  have hOldCut : Disjoint (L.record i).edgeSet
      (GroundingCut.CE L.cutFragmentInput (L.cutFragmentTags C)) := by
    simpa only [L.cutFragmentTags_CE C] using hEdges
  refine ⟨hOldCut, ?_⟩
  ext x
  constructor
  · intro hx
    refine ⟨hx, ?_⟩
    have hsegment : ∃ q : FinitePath G.graph,
        q.start = (L.record i).initial ∧ q.finish = x ∧ q.edgeSet ⊆ (L.record i).edgeSet := by
      by_cases hix : (L.record i).initial = x
      · refine ⟨FinitePath.trivial G.graph (L.record i).initial, rfl, hix, ?_⟩
        exact Set.empty_subset _
      · exact GroundingCutDecoder.exists_forward_segment_of_before
          ⟨GroundingFragmentWarp.initial_beforeEq_of_mem hx, hix⟩
    obtain ⟨q, hqs, hqx, hqE⟩ := hsegment
    refine ⟨q, Or.inl ⟨hqs, hqx⟩, ?_, hqE, hOldCut.mono_left hqE⟩
    intro z hz
    by_cases hzs : z = q.start
    · exact (hzs.trans hqs).symm ▸ (L.record i).initial_mem_support
    · obtain ⟨y, hyz⟩ := FinitePath.exists_incoming_edge_of_mem_support_of_ne_start q hz hzs
      exact ((L.record i).edgeSet_subset_support_prod (hqE hyz)).2
  · exact And.left

def fragmentCarrier (C : Set L.Vertex) (P : L.CutFragment) : Set L.Vertex
  | .source i => L.record i = P.parent ∧ i ∉ L.badRecords C
  | .edge e => e.1 ∈ P.path.edgeSet
  | _ => False

theorem fragmentCarrier_countable (C : Set L.Vertex) (P : L.CutFragment) :
    (L.fragmentCarrier C P).Countable := by
  have hsource : ({i : I | L.record i = P.parent ∧ i ∉ L.badRecords C} : Set I).Subsingleton := by
    intro i hi j hj
    exact L.record_injective (hi.1.trans hj.1.symm)
  apply ((L.fragmentEdgeVertices_countable P).union
    (hsource.countable.image Vertex.source)).mono
  intro a ha
  cases a with
  | source i => exact Or.inr ⟨i, ha, rfl⟩
  | edge e => exact Or.inl ha
  | marker y => exact ha.elim
  | off x => exact ha.elim

theorem fragmentCarrier_disjoint_cut (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.cutFragments C) : Disjoint (L.fragmentCarrier C P) C := by
  apply Set.disjoint_left.mpr
  intro a ha haC
  cases a with
  | source i => exact ha.2 (Or.inl haC)
  | edge e => exact Set.disjoint_left.mp (L.cutFragment_edges_disjoint C hP) ha ⟨e.2, haC⟩
  | marker y => exact ha.elim
  | off x => exact ha.elim

theorem fragmentCarrier_eq_of_common (C : Set L.Vertex) {P Q : L.CutFragment}
    (hP : P ∈ L.cutFragments C) (hQ : Q ∈ L.cutFragments C)
    {x : V} (hxP : x ∈ P.path.support) (hxQ : x ∈ Q.path.support) :
    L.fragmentCarrier C P = L.fragmentCarrier C Q := by
  have hparent := (L.cutFragment_parent_and_support_eq_of_common C hP hQ hxP hxQ).1
  have hEdges := L.cutFragment_edgeSet_eq_of_common C hP hQ hxP hxQ
  ext a
  cases a with
  | source i =>
      change (L.record i = P.parent ∧ i ∉ L.badRecords C) ↔
        (L.record i = Q.parent ∧ i ∉ L.badRecords C)
      rw [hparent]
  | edge e =>
      change e.1 ∈ P.path.edgeSet ↔ e.1 ∈ Q.path.edgeSet
      rw [hEdges]
  | marker y => rfl
  | off x => rfl

/-- With no cut owner edge, maximality makes every fragment of that
record the entire record. This includes singleton paths and rays. -/
theorem fragmentCarrier_eq_recordCarrier (C : Set L.Vertex) {P : L.CutFragment}
    (hP : P ∈ L.cutFragments C) (i : I) (hi : i ∉ L.badRecords C)
    (hparent : P.parent = L.record i) :
    L.fragmentCarrier C P = L.recordCarrier i := by
  have hx : P.path.initial ∈ (L.record i).support :=
    hparent ▸ P.support_subset P.path.initial_mem_support
  have hEdges : P.path.edgeSet = (L.record i).edgeSet :=
    L.cutFragment_edgeSet_eq_of_common C hP (L.recordFragment_mem C i hi)
      P.path.initial_mem_support hx
  ext a
  cases a with
  | source j =>
      change (L.record j = P.parent ∧ j ∉ L.badRecords C) ↔ j = i
      rw [hparent]
      constructor
      · exact fun h ↦ L.record_injective h.1
      · rintro rfl
        exact ⟨rfl, hi⟩
  | edge e =>
      change e.1 ∈ P.path.edgeSet ↔ e.1 ∈ (L.record i).edgeSet
      rw [hEdges]
  | marker y => rfl
  | off x => rfl

#print axioms recordFragment_mem
#print axioms fragmentCarrier_countable
#print axioms fragmentCarrier_disjoint_cut
#print axioms fragmentCarrier_eq_recordCarrier

end Erdos599.GroundingAllMarkerAuxiliary.Input
