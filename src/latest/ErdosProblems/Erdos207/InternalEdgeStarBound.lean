/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeGreedyObstruction
import ErdosProblems.Erdos207.InternalEdgeReserve

/-!
# Vertex-star control for an internal-edge greedy prefix

Every triangle inserted during the stage belongs to the available family,
and every available triangle is a triangle of the residual graph.  Thus the
new covered graph is a subgraph of the residual graph.  Packinghood then
turns graph-degree control into the selected-star bound used in the relative
obstruction estimate.
-/

namespace Erdos207

open Finset

noncomputable section

/-- A family consisting of triangles of `G` covers only edges of `G`. -/
lemma ConsistsOfTriangles.coveredGraph_le
    {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {C : TripleSystemOn V}
    (hC : ConsistsOfTriangles G C) : coveredGraph C ≤ G := by
  intro u v huv
  obtain ⟨T, hTC, huT, hvT, huvne⟩ := coveredGraph_adj.mp huv
  exact hC T hTC u huT v hvT huvne

/-- Removing the initial family from a reachable stage prefix leaves only
triangles from the ambient available family. -/
lemma sdiff_initial_subset_available
    {V : Type*} [DecidableEq V]
    {P₀ A Q : TripleSystemOn V} (hQ : Q ⊆ P₀ ∪ A) :
    Q \ P₀ ⊆ A := by
  intro T hT
  obtain ⟨hTQ, hTnot⟩ := mem_sdiff.mp hT
  rcases mem_union.mp (hQ hTQ) with hTP₀ | hTA
  · exact (hTnot hTP₀).elim
  · exact hTA

/-- A star in the new part of a stage prefix is bounded by the corresponding
residual-graph degree. -/
theorem card_triplesThrough_sdiff_le_graph_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A P₀ Q : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A) (hpacking : IsPackingOn Q)
    (hsub : Q ⊆ P₀ ∪ A) (v : V) :
    (triplesThrough (Q \ P₀) v).card ≤ G.degree v := by
  classical
  have hnewA : Q \ P₀ ⊆ A := sdiff_initial_subset_available hsub
  have htriNew : ConsistsOfTriangles G (Q \ P₀) := by
    intro T hT
    exact htri T (hnewA hT)
  have hpackingNew : IsPackingOn (Q \ P₀) := hpacking.mono sdiff_subset
  have hdegree : (coveredGraph (Q \ P₀)).degree v ≤ G.degree v :=
    SimpleGraph.degree_le_of_le htriNew.coveredGraph_le
  rw [hpackingNew.coveredGraph_degree_eq_two_mul_triplesThrough] at hdegree
  omega

/-- A uniform residual degree cutoff controls both endpoint stars of every
internal edge. -/
theorem internalOuterEdge_new_endpoint_stars_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A P₀ Q : TripleSystemOn V} {U : Finset V}
    (htri : ConsistsOfTriangles G A) (hpacking : IsPackingOn Q)
    (hsub : Q ⊆ P₀ ∪ A) {d : ℕ}
    (hdegree : ∀ v : V, G.degree v ≤ d)
    (e : Sym2 V) (_he : e ∈ internalOuterEdges G U) :
    (triplesThrough (Q \ P₀) e.out.1).card ≤ d ∧
      (triplesThrough (Q \ P₀) e.out.2).card ≤ d := by
  constructor
  · exact (card_triplesThrough_sdiff_le_graph_degree
      htri hpacking hsub e.out.1).trans (hdegree e.out.1)
  · exact (card_triplesThrough_sdiff_le_graph_degree
      htri hpacking hsub e.out.2).trans (hdegree e.out.2)

end

end Erdos207
