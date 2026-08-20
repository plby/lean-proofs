/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.HybridLargeSieve

/-!
# Finite cutoff energy for Gallagher's zero detector

Gallagher's log-free density argument does not sample a Dirichlet polynomial
only at the ordinates of the zeros.  It first removes the smooth detector
weight by partial summation.  The resulting partial sums are then averaged
over their upper cutoff.  This file supplies the exact finite Abel identity
and the weighted Cauchy--Schwarz inequality used in that reduction.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

/-- Finite Abel summation on the integer interval `(A, N]`. -/
theorem sum_Ioc_mul_eq_prefix_mul_add_sum_prefix_mul_sub
    {R : Type*} [CommRing R] (f w : ℕ → R) {A N : ℕ} (hAN : A ≤ N) :
    (∑ n ∈ Finset.Ioc A N, f n * w n) =
      (∑ n ∈ Finset.Ioc A N, f n) * w N +
        ∑ m ∈ Finset.Ico A N,
          (∑ n ∈ Finset.Ioc A m, f n) * (w m - w (m + 1)) := by
  induction N, hAN using Nat.le_induction with
  | base => simp
  | succ N hAN ih =>
      rw [Finset.sum_Ioc_succ_top hAN, Finset.sum_Ico_succ_top hAN]
      rw [Finset.sum_Ioc_succ_top hAN, ih]
      ring

/-- Complex Cauchy--Schwarz in product form. -/
theorem norm_sum_mul_sq_le_sum_norm_sq_mul_sum_norm_sq
    {κ : Type*} (S : Finset κ) (x y : κ → ℂ) :
    ‖∑ k ∈ S, x k * y k‖ ^ 2 ≤
      (∑ k ∈ S, ‖x k‖ ^ 2) * ∑ k ∈ S, ‖y k‖ ^ 2 := by
  calc
    ‖∑ k ∈ S, x k * y k‖ ^ 2 ≤
        (∑ k ∈ S, ‖x k * y k‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ = (∑ k ∈ S, ‖x k‖ * ‖y k‖) ^ 2 := by
      simp only [norm_mul]
    _ ≤ (∑ k ∈ S, ‖x k‖ ^ 2) *
        ∑ k ∈ S, ‖y k‖ ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq S
        (fun k ↦ ‖x k‖) (fun k ↦ ‖y k‖)

/-- Weighted complex Cauchy--Schwarz.  This formulation permits `x k = 0`;
only the externally chosen weights must be positive. -/
theorem norm_sum_mul_sq_le_weighted
    {κ : Type*} (S : Finset κ) (a : κ → ℝ)
    (ha : ∀ k ∈ S, 0 < a k) (x y : κ → ℂ) :
    ‖∑ k ∈ S, x k * y k‖ ^ 2 ≤
      (∑ k ∈ S, ‖x k‖ ^ 2 / a k) *
        ∑ k ∈ S, a k * ‖y k‖ ^ 2 := by
  let r : κ → ℝ := fun k ↦ Real.sqrt (a k)
  let X : κ → ℂ := fun k ↦ x k / (r k : ℂ)
  let Y : κ → ℂ := fun k ↦ (r k : ℂ) * y k
  have hrpos : ∀ k ∈ S, 0 < r k := by
    intro k hk
    exact Real.sqrt_pos.2 (ha k hk)
  have hxy : ∀ k ∈ S, X k * Y k = x k * y k := by
    intro k hk
    dsimp [X, Y]
    rw [div_mul_eq_mul_div]
    field_simp [show (r k : ℂ) ≠ 0 by
      exact_mod_cast (hrpos k hk).ne']
  have hX : ∀ k ∈ S, ‖X k‖ ^ 2 = ‖x k‖ ^ 2 / a k := by
    intro k hk
    dsimp [X, r]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (ha k hk))]
    rw [div_pow, Real.sq_sqrt (ha k hk).le]
  have hY : ∀ k ∈ S, ‖Y k‖ ^ 2 = a k * ‖y k‖ ^ 2 := by
    intro k hk
    dsimp [Y, r]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (ha k hk)), mul_pow,
      Real.sq_sqrt (ha k hk).le]
  rw [← Finset.sum_congr rfl hxy]
  refine (norm_sum_mul_sq_le_sum_norm_sq_mul_sum_norm_sq S X Y).trans_eq ?_
  congr 1
  · exact Finset.sum_congr rfl hX
  · exact Finset.sum_congr rfl hY

/-- The exact finite cutoff-energy inequality used by the Gallagher route.
The first factor is logarithmic `L²` energy of the partial sums, with measure
`1 / m`; the second is the variation energy of the smooth weight, with
measure `m`. -/
theorem norm_sum_Ioc_mul_sq_le_partialSumEnergy_mul_weightVariation
    (f w : ℕ → ℂ) {A N : ℕ} (hA : 0 < A) (hAN : A ≤ N) :
    ‖∑ n ∈ Finset.Ioc A N, f n * w n‖ ^ 2 ≤
      (∑ m ∈ Finset.Icc A N,
          ‖∑ n ∈ Finset.Ioc A m, f n‖ ^ 2 / (m : ℝ)) *
        ((N : ℝ) * ‖w N‖ ^ 2 +
          ∑ m ∈ Finset.Ico A N,
            (m : ℝ) * ‖w m - w (m + 1)‖ ^ 2) := by
  let P : ℕ → ℂ := fun m ↦ ∑ n ∈ Finset.Ioc A m, f n
  let d : ℕ → ℂ := fun m ↦ if m = N then w N else w m - w (m + 1)
  have hpos : ∀ m ∈ Finset.Icc A N, 0 < (m : ℝ) := by
    intro m hm
    exact_mod_cast hA.trans_le (Finset.mem_Icc.mp hm).1
  have hsplit :
      (∑ m ∈ Finset.Icc A N, P m * d m) =
        P N * w N + ∑ m ∈ Finset.Ico A N, P m * (w m - w (m + 1)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top hAN]
    simp only [d, P, if_pos, add_comm]
    apply congrArg (fun z : ℂ ↦ P N * w N + z)
    apply Finset.sum_congr rfl
    intro m hm
    rw [if_neg]
    exact ne_of_lt (Finset.mem_Ico.mp hm).2
  have hvariation :
      (∑ m ∈ Finset.Icc A N, (m : ℝ) * ‖d m‖ ^ 2) =
        (N : ℝ) * ‖w N‖ ^ 2 +
          ∑ m ∈ Finset.Ico A N,
            (m : ℝ) * ‖w m - w (m + 1)‖ ^ 2 := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_succ_top hAN]
    simp only [d, if_pos, add_comm]
    apply congrArg (fun z : ℝ ↦ (N : ℝ) * ‖w N‖ ^ 2 + z)
    apply Finset.sum_congr rfl
    intro m hm
    rw [if_neg]
    exact ne_of_lt (Finset.mem_Ico.mp hm).2
  rw [sum_Ioc_mul_eq_prefix_mul_add_sum_prefix_mul_sub f w hAN]
  rw [← hsplit]
  have hcauchy := norm_sum_mul_sq_le_weighted
    (Finset.Icc A N) (fun m ↦ (m : ℝ)) hpos P d
  simpa only [P, hvariation] using hcauchy

end

end Erdos48
