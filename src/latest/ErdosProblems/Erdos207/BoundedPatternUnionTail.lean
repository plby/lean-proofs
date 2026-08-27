/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BoundedPatternIndex
import ErdosProblems.Erdos207.SourceQuasiForbiddenOrders

/-! # Polynomial union bounds over all bounded-support patterns and their edges -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem FiniteLaw.probability_exists_boundedPatternEdge_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (h : ℕ) (Event : BoundedGraphPattern V h → Sym2 V → Ω → Prop)
    (epsilon : ℝ≥0) (hbound : ∀ Q, ∀ e ∈ graphEdges Q.1, L.probability (Event Q e) ≤ epsilon) :
    L.probability (fun ω ↦ ∃ Q : BoundedGraphPattern V h, ∃ e ∈ graphEdges Q.1, Event Q e ω) ≤
      ((h^2 + 1 : ℕ) * (Fintype.card V + 1 : ℝ≥0) ^ (2*h^2)) * h^2 * epsilon := by
  have hpoint : ∀ Q : BoundedGraphPattern V h,
      L.probability (fun ω ↦ ∃ e ∈ graphEdges Q.1, Event Q e ω) ≤ (h^2 : ℕ) * epsilon := by
    intro Q
    calc
      _ ≤ ∑ e ∈ graphEdges Q.1, L.probability (Event Q e) := L.probability_exists_le _ _
      _ ≤ ∑ _e ∈ graphEdges Q.1, epsilon := sum_le_sum (hbound Q)
      _ = (graphEdges Q.1).card * epsilon := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ zero_le
        exact_mod_cast (card_graphEdges_le_graphSupportFinset_sq Q.1).trans (Nat.pow_le_pow_left Q.2 2)
  have hb := (L.probability_exists_le (univ : Finset (BoundedGraphPattern V h))
    (fun Q ω ↦ ∃ e ∈ graphEdges Q.1, Event Q e ω)).trans (sum_le_sum (fun Q _ ↦ hpoint Q))
  simp only [mem_univ, true_and, sum_const, card_univ, nsmul_eq_mul] at hb
  apply hb.trans
  have hc : (Fintype.card (BoundedGraphPattern V h) : ℝ≥0) ≤
      (h^2 + 1 : ℕ) * (Fintype.card V + 1 : ℝ≥0) ^ (2*h^2) := by
    exact_mod_cast card_boundedGraphPattern_le_polynomial V h
  calc
    _ ≤ (((h^2 + 1 : ℕ) : ℝ≥0) * (Fintype.card V + 1 : ℝ≥0) ^ (2*h^2)) * ((h^2 : ℕ) * epsilon) := by gcongr
    _ = _ := by push_cast; ring

theorem FiniteLaw.probability_not_all_boundedPatternQuasi_le
    {Ω J V : Type*} [Fintype Ω] [DecidableEq J] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (orders : Finset J) (F : J → ForbiddenFamilyOn V)
    (S : Finset V) (G : SimpleGraph V) (I D : Ω → TripleSystemOn V) (h : ℕ)
    (cutoff : BoundedGraphPattern V h → J → ℝ≥0) (error : J → ℝ≥0)
    (hbound : ∀ Q, ∀ e ∈ graphEdges Q.1, ∀ j ∈ orders,
      L.probability (fun ω ↦ cutoff Q j <
        (sourceQuasiObstructedVertices W (F j) e S (graphSupportFinset Q.1) G (I ω) (D ω)).card) ≤ error j) :
    L.probability (fun ω ↦ ¬ ∀ Q : BoundedGraphPattern V h, ∀ e ∈ graphEdges Q.1,
      ((sourceQuasiObstructedVertices W (orders.biUnion F) e S (graphSupportFinset Q.1) G (I ω) (D ω)).card : ℝ≥0) ≤
        ∑ j ∈ orders, cutoff Q j) ≤
      ((h^2 + 1 : ℕ) * (Fintype.card V + 1 : ℝ≥0) ^ (2*h^2)) * h^2 * ∑ j ∈ orders, error j := by
  have hb := L.probability_exists_boundedPatternEdge_le h
    (fun Q e ω ↦ (∑ j ∈ orders, cutoff Q j) <
      (sourceQuasiObstructedVertices W (orders.biUnion F) e S (graphSupportFinset Q.1) G (I ω) (D ω)).card)
    (∑ j ∈ orders, error j) (fun Q e he ↦
      L.sourceQuasiForbiddenOrders_probability_le W orders F e S (graphSupportFinset Q.1) G I D
        (cutoff Q) error (hbound Q e he))
  apply le_trans _ hb
  apply L.probability_mono
  intro ω hω
  simpa only [not_forall, not_le, exists_prop] using hω

end

end Erdos207
