/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkJointGeometry
import ErdosProblems.Erdos207.SupportedTypicalResidualLinks

/-! # The source geometry certificate follows from an actual intermediate master state -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

theorem ConsistsOfTriangles.triple_edges_subset
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A) {T : TripleOn V} (hT : T ∈ A) :
    tripleEdgeFinset T ⊆ graphEdges G := by
  intro e he
  induction e using Sym2.ind with
  | h u v =>
    have hh := mk_mem_tripleEdgeFinset_iff.mp he
    exact mem_graphEdges_iff.mpr (htri T hT u hh.1 v hh.2.1 hh.2.2)

theorem ConsistsOfTriangles.triple_vertices_subset
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A) {current : Finset V} (hsupp : GraphSupportedOn G (current : Set V))
    {T : TripleOn V} (hT : T ∈ A) : T.1 ⊆ current :=
  triple_supported_of_graph_edges G current T hsupp (htri.triple_edges_subset hT)

theorem rawLinkSourceGeometry_of_intermediate
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell+1)} {Gamma G : SimpleGraph V} {U : Finset V}
    {I D R A : TripleSystemOn V} {reserve : Finset (Sym2 V)}
    {K : {x : V // x ∉ U} → BipartiteLink V}
    (hstate : IsIntermediateLinkState G U A I D R K)
    (hleft : ∀ o, (K o).left ⊆ U) (hright : ∀ o, (K o).right ⊆ U)
    (hspokes : ∀ o, (K o).SpokesIn reserve)
    (hG : G ≤ Gamma) (hsupp : GraphSupportedOn G (W.U k : Set V)) (htri : ConsistsOfTriangles G A)
    (orders : Finset ℕ) (F : ℕ → ForbiddenFamilyOn V)
    (hinitial : ∀ T ∈ A, ¬ CompletesForbidden (orders.biUnion F) (I ∪ D) T) :
    RawLinkSourceGeometry W k Gamma U I (D ∪ R) D A reserve (outsideVertexEmbedding U) K orders F := by
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  refine ⟨fun o ↦ (hstate.1 o).1, fun o ↦ o.2, hleft, hright, hspokes, ?_,
    fun T hT u hu v hv huv ↦ hG (htri T hT u hu v hv huv),
    fun T hT ↦ htri.triple_vertices_subset hsupp hT, ?_, ?_⟩
  · intro o
    have hres : (K o).left ∪ (K o).right ⊆ residualNeighbors G R o.1 := (hstate.1 o).2.1.le
    constructor
    · intro x hx
      rw [(hstate.1 o).1]
      exact mem_graphEdges_iff.mpr (hG (mem_residualNeighbors_iff.mp (hres (mem_union_left _ hx))).1)
    · intro x hx
      rw [(hstate.1 o).1]
      exact mem_graphEdges_iff.mpr (hG (mem_residualNeighbors_iff.mp (hres (mem_union_right _ hx))).1)
  · intro j hj T hT hcomplete
    obtain ⟨S, hS, hTS, hsub⟩ := hcomplete
    exact hinitial T hT ⟨S, mem_biUnion.mpr ⟨j, hj, hS⟩, hTS, hsub⟩
  · intro T hT
    have hTR : T ∈ R := (mem_union.mp (mem_sdiff.mp hT).1).resolve_left (mem_sdiff.mp hT).2
    exact W.prefix_level_eq_last_of_subset k T (htri.triple_vertices_subset hsupp (hstate.2.1 hTR))

end

end Erdos207
