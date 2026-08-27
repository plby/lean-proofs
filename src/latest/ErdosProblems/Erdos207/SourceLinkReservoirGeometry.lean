/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RawSampledLinkJointLaw
import ErdosProblems.Erdos207.SourceLinkRealizedCoordinates
import ErdosProblems.Erdos207.VortexShellGeometry

/-! # Source marked-moment geometry of the actual retained link reservoir -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

def sourceLinkAmbientCandidates {V : Type*} [Fintype V] [DecidableEq V]
    (current U : Finset V) : TripleSystemOn V :=
  univ.filter fun T ↦ T.1 ⊆ current ∧ (T.1 ∩ U).card = 2

theorem mem_sourceLinkAmbientCandidates_iff
    {V : Type*} [Fintype V] [DecidableEq V] {current U : Finset V} {T : TripleOn V} :
    T ∈ sourceLinkAmbientCandidates current U ↔ T.1 ⊆ current ∧ (T.1 ∩ U).card = 2 := by
  simp only [sourceLinkAmbientCandidates, mem_filter, mem_univ, true_and]

theorem sourceLinkAmbientCandidates_terminal
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell+1)) (U : Finset V) :
    ∀ T ∈ sourceLinkAmbientCandidates (W.U k) U, (W.prefix k).level T = Fin.last k.val := by
  intro T hT
  exact W.prefix_level_eq_last_of_subset k T (mem_sourceLinkAmbientCandidates_iff.mp hT).1

theorem IsSimultaneousLinkFamily.card_inner_vertices
    {O V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {center : O ↪ V} {K : O → BipartiteLink V}
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    {M : TripleSystemOn V} (hfamily : IsSimultaneousLinkFamily K M) :
    ∀ T ∈ M, (T.1 ∩ U).card = 2 := by
  intro T hT
  obtain ⟨⟨o,a,b⟩, rfl⟩ := hfamily T hT
  have hc : (K o).center ∉ U := by simpa only [hcenter o] using hout o
  have ha : (K o).leftEmbedding a ∈ U := hleft o a.2
  have hb : (K o).rightEmbedding b ∈ U := hright o b.2
  have heq : (simultaneousLinkPairTriple K ⟨o,(a,b)⟩).1 ∩ U =
      {(K o).leftEmbedding a, (K o).rightEmbedding b} := by
    ext v
    simp only [mem_inter, simultaneousLinkPairTriple, mem_linkMatchingTriple_iff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hv, hvU⟩
      rcases hv with rfl | hv | hv
      · exact (hc hvU).elim
      · exact Or.inl hv
      · exact Or.inr hv
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), ha⟩
      · exact ⟨Or.inr (Or.inr rfl), hb⟩
  rw [heq]
  simp only [card_pair_eq_two_iff]
  exact (K o).left_ne_right a b

theorem IsSampledLinkJointOutcome.reservoir_subset_sourceAmbient
    {O V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {available P : TripleSystemOn V} {K : O → BipartiteLink V}
    {z : TripleSystemOn V × TripleSystemOn V}
    (hstruct : IsSampledLinkJointOutcome F available P K z)
    {G : SimpleGraph V} {current U : Finset V} {center : O ↪ V}
    (htri : ConsistsOfTriangles G available) (hsupp : GraphSupportedOn G (current : Set V))
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U) :
    z.1 ⊆ sourceLinkAmbientCandidates current U := by
  intro T hT
  apply mem_sourceLinkAmbientCandidates_iff.mpr
  refine ⟨triple_supported_of_graph_edges G current T hsupp ?_,
    hstruct.reservoir_family.card_inner_vertices hcenter hout hleft hright T hT⟩
  intro e he
  induction e using Sym2.ind with
  | h u v =>
    have hh := mk_mem_tripleEdgeFinset_iff.mp he
    exact mem_graphEdges_iff.mpr (htri T (hstruct.reservoir_available hT) u hh.1 v hh.2.1 hh.2.2)

theorem IsSampledLinkJointOutcome.reservoir_retainedEdges
    {O V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {available I D : TripleSystemOn V} {K : O → BipartiteLink V}
    {z : TripleSystemOn V × TripleSystemOn V}
    (hstruct : IsSampledLinkJointOutcome F available (I ∪ D) K z)
    {G : SimpleGraph V} {U : Finset V} {center : O ↪ V} {reserve : Finset (Sym2 V)}
    (htri : ConsistsOfTriangles G available)
    (hcenter : ∀ o, (K o).center = center o) (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (hspokes : ∀ o, (K o).SpokesIn reserve) :
    z.1.biUnion tripleEdgeFinset ⊆ sourceLinkRetainedEdges G U I D reserve := by
  have hcross := hstruct.reservoir_family.familyCrossingEdges_subset hcenter hout hleft hright hspokes
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_biUnion.mp he
  induction e using Sym2.ind with
  | h u v =>
    have hh := mk_mem_tripleEdgeFinset_iff.mp heT
    apply mem_filter.mpr
    refine ⟨mem_graphEdges_iff.mpr (htri T (hstruct.reservoir_available hT) u hh.1 v hh.2.1 hh.2.2), ?_, ?_⟩
    · exact hstruct.reservoir_pair_safe T hT u hh.1 v hh.2.1 hh.2.2
    · intro hc
      exact hcross (mem_biUnion.mpr ⟨T, hT, mem_filter.mpr ⟨heT, hc⟩⟩)

end

end Erdos207
