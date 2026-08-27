/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyObstructionCount
import ErdosProblems.Erdos207.CompatibleCandidateDegree

/-!
# Edge obstructions relative to an initial packing

At the start of KSSS Section 10.2 every available triangle is already
edge-disjoint from the previously chosen packing.  Consequently, when a
candidate later becomes edge-blocked, the blocking edge is covered by a
triangle inserted during the current greedy stage.  The lemmas below remove
the (typically much larger) initial packing from the degree loss.
-/

namespace Erdos207

open Finset

noncomputable section

/-- If every ambient candidate avoids the pairs covered by `P₀`, then an
edge-blocked candidate at a later family `Q` is adjacent to an endpoint in
the graph covered by the genuinely new family `Q \ P₀`. -/
lemma edgeBlockedThirdVertex_mem_new_neighbor_union
    {V : Type*} [Fintype V] [DecidableEq V]
    {A P₀ Q : TripleSystemOn V} {u v : V}
    (hinitial : ∀ T ∈ A,
      TriangleAvoidsGraph (coveredGraph P₀) T)
    (huv : (leaveGraph Q).Adj u v) {w : ThirdVertex u v}
    (hw : w ∈ edgeBlockedThirdVertices A Q huv.ne) :
    w.1 ∈ (coveredGraph (Q \ P₀)).neighborFinset u ∪
      (coveredGraph (Q \ P₀)).neighborFinset v := by
  have hTA := (mem_edgeBlockedThirdVertices_iff.mp hw).1
  have hwold := edgeBlockedThirdVertex_mem_neighbor_union huv hw
  rw [mem_union] at hwold ⊢
  rcases hwold with hwu | hwv
  · apply Or.inl
    rw [SimpleGraph.mem_neighborFinset] at hwu ⊢
    obtain ⟨R, hRQ, huR, hwR, huw⟩ := coveredGraph_adj.mp hwu
    have hRnot : R ∉ P₀ := by
      intro hRP₀
      exact hinitial (thirdVertexTriple huv.ne w) hTA
        u (left_mem_thirdVertexTriple huv.ne w)
        w.1 (third_mem_thirdVertexTriple huv.ne w) w.2.1.symm
        (coveredGraph_adj.mpr ⟨R, hRP₀, huR, hwR, huw⟩)
    exact coveredGraph_adj.mpr
      ⟨R, mem_sdiff.mpr ⟨hRQ, hRnot⟩, huR, hwR, huw⟩
  · apply Or.inr
    rw [SimpleGraph.mem_neighborFinset] at hwv ⊢
    obtain ⟨R, hRQ, hvR, hwR, hvw⟩ := coveredGraph_adj.mp hwv
    have hRnot : R ∉ P₀ := by
      intro hRP₀
      exact hinitial (thirdVertexTriple huv.ne w) hTA
        v (right_mem_thirdVertexTriple huv.ne w)
        w.1 (third_mem_thirdVertexTriple huv.ne w) w.2.2.symm
        (coveredGraph_adj.mpr ⟨R, hRP₀, hvR, hwR, hvw⟩)
    exact coveredGraph_adj.mpr
      ⟨R, mem_sdiff.mpr ⟨hRQ, hRnot⟩, hvR, hwR, hvw⟩

/-- Relative neighbor-union bound for pair conflicts. -/
theorem card_edgeBlockedThirdVertices_le_new_neighbor_union
    {V : Type*} [Fintype V] [DecidableEq V]
    {A P₀ Q : TripleSystemOn V} {u v : V}
    (hinitial : ∀ T ∈ A,
      TriangleAvoidsGraph (coveredGraph P₀) T)
    (huv : (leaveGraph Q).Adj u v) :
    (edgeBlockedThirdVertices A Q huv.ne).card ≤
      ((coveredGraph (Q \ P₀)).neighborFinset u ∪
        (coveredGraph (Q \ P₀)).neighborFinset v).card := by
  let e : ThirdVertex u v ↪ V := Function.Embedding.subtype _
  have hsub : (edgeBlockedThirdVertices A Q huv.ne).map e ⊆
      (coveredGraph (Q \ P₀)).neighborFinset u ∪
        (coveredGraph (Q \ P₀)).neighborFinset v := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hx
    exact edgeBlockedThirdVertex_mem_new_neighbor_union hinitial huv hw
  simpa using card_le_card hsub

/-- Degree-sum form of the relative obstruction bound. -/
theorem card_edgeBlockedThirdVertices_le_new_degree_add
    {V : Type*} [Fintype V] [DecidableEq V]
    {A P₀ Q : TripleSystemOn V} {u v : V}
    (hinitial : ∀ T ∈ A,
      TriangleAvoidsGraph (coveredGraph P₀) T)
    (huv : (leaveGraph Q).Adj u v) :
    (edgeBlockedThirdVertices A Q huv.ne).card ≤
      (coveredGraph (Q \ P₀)).degree u +
        (coveredGraph (Q \ P₀)).degree v := by
  calc
    (edgeBlockedThirdVertices A Q huv.ne).card ≤
        ((coveredGraph (Q \ P₀)).neighborFinset u ∪
          (coveredGraph (Q \ P₀)).neighborFinset v).card :=
      card_edgeBlockedThirdVertices_le_new_neighbor_union hinitial huv
    _ ≤ ((coveredGraph (Q \ P₀)).neighborFinset u).card +
          ((coveredGraph (Q \ P₀)).neighborFinset v).card :=
      card_union_le _ _
    _ = (coveredGraph (Q \ P₀)).degree u +
          (coveredGraph (Q \ P₀)).degree v := by
      rw [SimpleGraph.card_neighborFinset_eq_degree,
        SimpleGraph.card_neighborFinset_eq_degree]

/-- For a later packing, the relative edge loss is twice the two new
triangle-star counts. -/
theorem card_edgeBlockedThirdVertices_le_two_mul_new_star_add
    {V : Type*} [Fintype V] [DecidableEq V]
    {A P₀ Q : TripleSystemOn V} (hQ : IsPackingOn Q) {u v : V}
    (hinitial : ∀ T ∈ A,
      TriangleAvoidsGraph (coveredGraph P₀) T)
    (huv : (leaveGraph Q).Adj u v) :
    (edgeBlockedThirdVertices A Q huv.ne).card ≤
      2 * (triplesThrough (Q \ P₀) u).card +
        2 * (triplesThrough (Q \ P₀) v).card := by
  have hnew : IsPackingOn (Q \ P₀) := hQ.mono sdiff_subset
  simpa [hnew.coveredGraph_degree_eq_two_mul_triplesThrough] using
    card_edgeBlockedThirdVertices_le_new_degree_add hinitial huv

end

end Erdos207
