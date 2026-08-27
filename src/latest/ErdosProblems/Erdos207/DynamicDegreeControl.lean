/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationDynamicMasterLinkStageGood

/-!
# Uniform degree control during the dynamic link sweep

A dynamically reached family consists only of the fixed pre-link packing and
triangles from the current available family.  Since every available triangle
is a triangle of the stage graph, its covered graph is contained in the union
of the old covered graph and the stage graph.  This makes the degree cutoffs
independent of the intermediate link state.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Degree is subadditive under a graph upper bound by a union. -/
lemma SimpleGraph.degree_le_add_of_le_sup
    {V : Type*} [Fintype V] [DecidableEq V]
    {K G H : SimpleGraph V} [DecidableRel K.Adj]
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : K ≤ G ⊔ H) (v : V) :
    K.degree v ≤ G.degree v + H.degree v := by
  have hneighbors : K.neighborFinset v ⊆ (G ⊔ H).neighborFinset v := by
    intro x hx
    rw [SimpleGraph.mem_neighborFinset] at hx ⊢
    exact h hx
  calc
    K.degree v ≤ (G ⊔ H).degree v := card_le_card hneighbors
    _ = #(G.neighborFinset v ∪ H.neighborFinset v) := by
      simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_sup]
    _ ≤ #(G.neighborFinset v) + #(H.neighborFinset v) := card_union_le _ _
    _ = G.degree v + H.degree v := rfl

/-- Every edge covered by a dynamically reached family is covered either by
the fixed pre-link packing or by a triangle of the current stage graph. -/
lemma coveredGraph_dynamic_le_old_sup_stage
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {F : ForbiddenFamilyOn V}
    {A I D R P : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A)
    (hstate : IsDynamicLinkState F A I D R P) :
    coveredGraph P ≤ coveredGraph (I ∪ (D ∪ R)) ⊔ G := by
  intro u v huv
  obtain ⟨T, hTP, huT, hvT, huvne⟩ := coveredGraph_adj.mp huv
  rcases mem_union.mp (hstate.2.1 hTP) with hTold | hTA
  · rw [SimpleGraph.sup_adj]
    exact Or.inl (coveredGraph_adj.mpr
      ⟨T, hTold, huT, hvT, huvne⟩)
  · rw [SimpleGraph.sup_adj]
    exact Or.inr (htri T hTA u huT v hvT huvne)

/-- Fixed old-graph and stage-graph degrees bound every dynamic covered
degree. -/
theorem coveredGraph_dynamic_degree_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {F : ForbiddenFamilyOn V}
    {A I D R P : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A)
    (hstate : IsDynamicLinkState F A I D R P) (v : V) :
    (coveredGraph P).degree v ≤
      (coveredGraph (I ∪ (D ∪ R))).degree v + G.degree v :=
  SimpleGraph.degree_le_add_of_le_sup
    (coveredGraph_dynamic_le_old_sup_stage htri hstate) v

/-- A fixed one-vertex budget discharges the statewise center-loss premise
of the dynamic master link theorem. -/
theorem dynamic_covered_degree_le_of_fixed_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {F : ForbiddenFamilyOn V}
    {A I D R P : TripleSystemOn V} {loss : ℕ}
    (htri : ConsistsOfTriangles G A)
    (hstate : IsDynamicLinkState F A I D R P)
    (hbudget : ∀ v : V,
      (coveredGraph (I ∪ (D ∪ R))).degree v + G.degree v ≤ loss)
    (v : V) : (coveredGraph P).degree v ≤ loss :=
  (coveredGraph_dynamic_degree_le htri hstate v).trans (hbudget v)

/-- A fixed two-vertex budget discharges both side-degree premises for every
residual bipartition at every dynamic state. -/
theorem dynamic_link_side_degrees_le_of_fixed_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {F : ForbiddenFamilyOn V}
    {A I D R P : TripleSystemOn V} {degreeCutoff : ℕ}
    (htri : ConsistsOfTriangles G A)
    (hstate : IsDynamicLinkState F A I D R P)
    (hbudget : ∀ u v : V,
      ((coveredGraph (I ∪ (D ∪ R))).degree u + G.degree u) +
        ((coveredGraph (I ∪ (D ∪ R))).degree v + G.degree v) ≤
          degreeCutoff)
    (K : BipartiteLink V) :
    (∀ a : ↥K.left,
      (coveredGraph P).degree K.center +
        (coveredGraph P).degree a.1 ≤ degreeCutoff) ∧
    (∀ b : ↥K.right,
      (coveredGraph P).degree K.center +
        (coveredGraph P).degree b.1 ≤ degreeCutoff) := by
  constructor
  · intro a
    exact (Nat.add_le_add
      (coveredGraph_dynamic_degree_le htri hstate K.center)
      (coveredGraph_dynamic_degree_le htri hstate a.1)).trans
        (hbudget K.center a.1)
  · intro b
    exact (Nat.add_le_add
      (coveredGraph_dynamic_degree_le htri hstate K.center)
      (coveredGraph_dynamic_degree_le htri hstate b.1)).trans
        (hbudget K.center b.1)

/-- Residual neighbors form a subset of the stage-graph neighborhood. -/
lemma residualNeighbors_card_le_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : TripleSystemOn V) (v : V) :
    (residualNeighbors G P v).card ≤ G.degree v := by
  apply card_le_card
  intro x hx
  rw [SimpleGraph.mem_neighborFinset]
  exact (mem_residualNeighbors_iff.mp hx).1

/-- A fixed stage-degree scalar implies the paired-bisection failure bound
at every dynamically reached state. -/
theorem dynamic_bisection_scalar_of_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : TripleSystemOn V) (v : V) (m d : ℕ)
    (hscalar : (G.degree v : ℝ≥0) *
      (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1) :
    ((residualNeighbors G P v).card : ℝ≥0) *
      (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1 := by
  apply lt_of_le_of_lt _ hscalar
  gcongr
  exact_mod_cast residualNeighbors_card_le_degree P v

end

end Erdos207
