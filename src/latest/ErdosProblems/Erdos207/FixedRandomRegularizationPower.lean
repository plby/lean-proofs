/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationInputFailurePower

/-! # Fixed-envelope averaging with every prescribed inverse-power error -/

namespace Erdos207

open Finset Filter
open scoped NNReal Topology

noncomputable section

def regularizationGapPowerError (j R t : ℕ) : ℝ≥0 :=
  2 * (t : ℝ≥0) ^ (R * j) * (Real.exp (-(t : ℝ))).toNNReal

theorem regularization_gap_failure_power_bound
    (t n m D j R : ℕ) (hj : 4 ≤ j) (hn : n ≤ t ^ R)
    (hm : m ≤ n ^ 3) (hD : D ≤ n ^ (j - 3)) :
    (D : ℝ) * (2 * m * Real.exp (-((8192 * t : ℕ) : ℝ) / 8192)) ≤
      regularizationGapPowerError j R t := by
  have hmR : (m : ℝ) ≤ ((t : ℝ) ^ R) ^ 3 := by
    exact_mod_cast hm.trans (Nat.pow_le_pow_left hn 3)
  have hDR : (D : ℝ) ≤ ((t : ℝ) ^ R) ^ (j - 3) := by
    exact_mod_cast hD.trans (Nat.pow_le_pow_left hn (j - 3))
  have hexp : -((8192 * t : ℕ) : ℝ) / 8192 = -(t : ℝ) := by push_cast; ring
  rw [hexp]
  calc
    _ ≤ ((t : ℝ) ^ R) ^ (j - 3) * (2 * ((t : ℝ) ^ R) ^ 3 * Real.exp (-(t : ℝ))) := by
      gcongr
    _ = 2 * (((t : ℝ) ^ R) ^ ((j - 3) + 3)) * Real.exp (-(t : ℝ)) := by rw [pow_add]; ring
    _ = 2 * (t : ℝ) ^ (R * j) * Real.exp (-(t : ℝ)) := by
      rw [Nat.sub_add_cancel (by omega : 3 ≤ j), ← pow_mul]
    _ = _ := by simp [regularizationGapPowerError, (Real.exp_pos _).le]

theorem sourceRandomFailureCoefficient_power_bound
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (j R t : ℕ) (hj : 4 ≤ j) (ht : 1 ≤ t)
    (hN : Fintype.card V ≤ t ^ R) :
    (sourceRandomFailureCoefficient W j : ℝ≥0) ≤
      (j + 3 : ℝ≥0) * 2 ^ (3 * j + 6) * (t : ℝ≥0) ^ (R * (3 * j + 6)) := by
  have htNN : (1 : ℝ≥0) ≤ t := by exact_mod_cast ht
  have hNR : (Fintype.card V : ℝ≥0) ≤ (t : ℝ≥0) ^ R := by exact_mod_cast hN
  have hplus : (Fintype.card V + 1 : ℝ≥0) ≤ 2 * (t : ℝ≥0) ^ R := by
    have hone := one_le_pow₀ htNN (n := R)
    exact (add_le_add hNR hone).trans_eq (by ring)
  calc
    _ ≤ (j + 3 : ℝ≥0) * (Fintype.card V + 1 : ℝ≥0) ^ (3 * j + 6) := by
      exact_mod_cast sourceRandomFailureCoefficient_le_polynomial W j hj
    _ ≤ (j + 3 : ℝ≥0) * (2 * (t : ℝ≥0) ^ R) ^ (3 * j + 6) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left' hplus _) zero_le
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

theorem eventually_fixedRandomRegularization_power_budget
    (j R decay : ℕ) (hj : 4 ≤ j) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}, ∀ W : Vortex V ell,
      Fintype.card V ≤ t ^ R →
      (sourceRandomFailureCoefficient W j : ℝ≥0) * ((2 : ℝ≥0) ^ t)⁻¹ +
        regularizationGapPowerError j R t / (1 / (t : ℝ≥0) ^ decay) < 1 := by
  have hfirst := polynomial_exp_neg_mul_tendsToZero 2 1 (R * j + decay) (by norm_num)
  have hsecond := (tendsto_pow_const_mul_const_pow_of_lt_one (R * (3 * j + 6))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
    ((j + 3 : ℝ) * 2 ^ (3 * j + 6))
  have hlim : Tendsto (fun t : ℕ ↦
      (j + 3 : ℝ) * 2 ^ (3 * j + 6) * (t : ℝ) ^ (R * (3 * j + 6)) * (1 / 2 : ℝ) ^ t +
        2 * (t : ℝ) ^ (R * j + decay) * Real.exp (-(t : ℝ))) atTop (𝓝 0) := by
    simpa only [one_mul, neg_one_mul, zero_add, mul_zero, mul_assoc] using hsecond.add hfirst
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨max 1 T, le_max_left _ _, ?_⟩
  intro t ht V _ _ ell W hN
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have hcoef := sourceRandomFailureCoefficient_power_bound W j R t hj ht1 hN
  have hsmall :
      (j + 3 : ℝ≥0) * 2 ^ (3 * j + 6) * (t : ℝ≥0) ^ (R * (3 * j + 6)) * (1 / 2 : ℝ≥0) ^ t +
        2 * (t : ℝ≥0) ^ (R * j + decay) * (Real.exp (-(t : ℝ))).toNNReal < 1 := by
    exact_mod_cast (by
      simpa only [Real.coe_toNNReal _ (Real.exp_pos _).le] using hT t ((le_max_right _ _).trans ht) :
        (j + 3 : ℝ) * 2 ^ (3 * j + 6) * (t : ℝ) ^ (R * (3 * j + 6)) * (1 / 2 : ℝ) ^ t +
          2 * (t : ℝ) ^ (R * j + decay) * ((Real.exp (-(t : ℝ))).toNNReal : ℝ) < 1)
  apply lt_of_le_of_lt _ hsmall
  apply add_le_add
  · simpa only [one_div, inv_pow] using mul_le_mul_of_nonneg_right hcoef
      (show 0 ≤ ((2 : ℝ≥0) ^ t)⁻¹ from zero_le)
  · exact le_of_eq (by simp only [regularizationGapPowerError, div_eq_mul_inv, inv_inv, one_mul, pow_add]; ring)

end

end Erdos207
