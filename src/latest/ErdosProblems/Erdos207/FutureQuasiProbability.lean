/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FutureTypicalityCaps

/-! # Simultaneous quasi-moment control over orders, pins, patterns, and future levels -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem FiniteLaw.probability_not_futureQuasiCaps_le
    {Ω J V : Type*} [Fintype Ω] [DecidableEq J] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (next : Fin (ell+1))
    (orders : Finset J) (F : J → ForbiddenFamilyOn V) (Γ : SimpleGraph V)
    (I D : Ω → TripleSystemOn V) (p eta epsilon : ℝ≥0) (h : ℕ)
    (cutoff : (Fin ell × Fin (ell+1)) → BoundedGraphPattern V h → J → ℝ≥0)
    (error : J → ℝ≥0)
    (hsum : ∀ a ∈ futureLevelPairs next, ∀ Q : BoundedGraphPattern V h,
      (∑ j ∈ orders, cutoff a Q j) ≤
        epsilon * p ^ (graphSupportFinset Q.1).card * eta ^ (graphEdges Q.1).card * (W.U a.2).card)
    (hpoint : ∀ a ∈ futureLevelPairs next, ∀ Q, ∀ e ∈ graphEdges Q.1, ∀ j ∈ orders,
      L.probability (fun ω ↦ cutoff a Q j <
        (sourceQuasiObstructedVertices (W.prefix a.1.castSucc) (F j) e (W.U a.2)
          (graphSupportFinset Q.1) Γ (I ω) (D ω)).card) ≤ error j) :
    L.probability (fun ω ↦ ¬ FutureQuasiCaps W next (orders.biUnion F) Γ (I ω) (D ω) p eta epsilon h) ≤
      (ell * (ell+1) : ℕ) *
        (((h^2+1 : ℕ) : ℝ≥0) * (Fintype.card V+1 : ℝ≥0) ^ (2*h^2)) * h^2 * ∑ j ∈ orders, error j := by
  let Bad := fun a : Fin ell × Fin (ell+1) ↦ fun ω ↦
    ¬ ∀ Q : BoundedGraphPattern V h, ∀ e ∈ graphEdges Q.1,
      ((sourceQuasiObstructedVertices (W.prefix a.1.castSucc) (orders.biUnion F) e (W.U a.2)
        (graphSupportFinset Q.1) Γ (I ω) (D ω)).card : ℝ≥0) ≤ ∑ j ∈ orders, cutoff a Q j
  let bound : ℝ≥0 := ((h^2+1 : ℕ) * (Fintype.card V+1 : ℝ≥0) ^ (2*h^2)) * h^2 * ∑ j ∈ orders, error j
  have hpair : ∀ a ∈ futureLevelPairs next, L.probability (Bad a) ≤ bound := by
    intro a ha
    exact L.probability_not_all_boundedPatternQuasi_le (W.prefix a.1.castSucc) orders F
      (W.U a.2) Γ I D h (cutoff a) error (hpoint a ha)
  have hcover : L.probability (fun ω ↦
      ¬ FutureQuasiCaps W next (orders.biUnion F) Γ (I ω) (D ω) p eta epsilon h) ≤
      L.probability (fun ω ↦ ∃ a ∈ futureLevelPairs next, Bad a ω) := by
    apply L.probability_mono
    intro ω hω
    by_contra hn
    apply hω
    intro a ha Q e he
    have hb : ¬ Bad a ω := fun h ↦ hn ⟨a, ha, h⟩
    have hc : ∀ Q : BoundedGraphPattern V h, ∀ e ∈ graphEdges Q.1,
        ((sourceQuasiObstructedVertices (W.prefix a.1.castSucc) (orders.biUnion F) e (W.U a.2)
          (graphSupportFinset Q.1) Γ (I ω) (D ω)).card : ℝ≥0) ≤ ∑ j ∈ orders, cutoff a Q j :=
      not_not.mp hb
    exact (hc Q e he).trans (hsum a ha Q)
  apply (hcover.trans ((L.probability_exists_le (futureLevelPairs next) Bad).trans (sum_le_sum hpair))).trans
  simp only [sum_const, nsmul_eq_mul]
  calc
    _ ≤ ((ell * (ell+1) : ℕ) : ℝ≥0) * bound := by
      gcongr
      exact_mod_cast card_futureLevelPairs_le next
    _ = _ := by dsimp only [bound]; ring

end

end Erdos207
