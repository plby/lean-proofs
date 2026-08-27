/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PolynomialExponentialDecay
import ErdosProblems.Erdos207.SourceRandomFailurePolynomial
import Mathlib.Analysis.SpecificLimits.Normed

/-! # The full regularization failure budget at polynomial vertex scales -/

namespace Erdos207

open Filter
open scoped Topology

theorem regularizationInput_failure_power_bound
    (t n N m D coeff j R : ℕ) (ht : 1 ≤ t) (hj : 4 ≤ j)
    (hn : n ≤ N) (hN : N ≤ t ^ R) (hm : m ≤ n ^ 3) (hD : D ≤ n ^ (j - 3))
    (hcoeff : coeff ≤ (j + 3) * (N + 1) ^ (3 * j + 6)) :
    (D : ℝ) * (2 * m * Real.exp (-((8192 * t : ℕ) : ℝ) / 8192)) +
      (coeff : ℝ) * ((2 : ℝ) ^ t)⁻¹ ≤
      2 * (t : ℝ) ^ (R * j) * Real.exp (-(t : ℝ)) +
        ((j + 3 : ℕ) : ℝ) * 2 ^ (3 * j + 6) * (t : ℝ) ^ (R * (3 * j + 6)) * (1 / 2 : ℝ) ^ t := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hNR : (N : ℝ) ≤ (t : ℝ) ^ R := by exact_mod_cast hN
  have hnR : (n : ℝ) ≤ (t : ℝ) ^ R := by exact_mod_cast hn.trans hN
  have hmR : (m : ℝ) ≤ ((t : ℝ) ^ R) ^ 3 := by
    exact_mod_cast hm.trans (Nat.pow_le_pow_left (hn.trans hN) 3)
  have hDR : (D : ℝ) ≤ ((t : ℝ) ^ R) ^ (j - 3) := by
    exact_mod_cast hD.trans (Nat.pow_le_pow_left (hn.trans hN) (j - 3))
  have hNplus : (N : ℝ) + 1 ≤ 2 * (t : ℝ) ^ R := by
    have hpow := one_le_pow₀ htR (n := R)
    linarith
  have hcoeffR : (coeff : ℝ) ≤ ((j + 3 : ℕ) : ℝ) * (2 * (t : ℝ) ^ R) ^ (3 * j + 6) := by
    have hc : (coeff : ℝ) ≤ ((j + 3 : ℕ) : ℝ) * ((N : ℝ) + 1) ^ (3 * j + 6) := by exact_mod_cast hcoeff
    exact hc.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hNplus _) (by positivity))
  have hexp : -((8192 * t : ℕ) : ℝ) / 8192 = -(t : ℝ) := by push_cast; ring
  rw [hexp]
  apply add_le_add
  · calc
      _ ≤ ((t : ℝ) ^ R) ^ (j - 3) * (2 * ((t : ℝ) ^ R) ^ 3 * Real.exp (-(t : ℝ))) := by gcongr
      _ = 2 * (((t : ℝ) ^ R) ^ ((j - 3) + 3)) * Real.exp (-(t : ℝ)) := by rw [pow_add]; ring
      _ = _ := by rw [Nat.sub_add_cancel (by omega : 3 ≤ j), ← pow_mul]
  · calc
      _ ≤ (((j + 3 : ℕ) : ℝ) * (2 * (t : ℝ) ^ R) ^ (3 * j + 6)) * ((2 : ℝ) ^ t)⁻¹ :=
        mul_le_mul_of_nonneg_right hcoeffR (by positivity)
      _ = _ := by simp only [mul_pow, ← pow_mul, one_div, inv_pow]; ring

theorem eventually_regularizationInput_failure_power_lt
    (j R : ℕ) : ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      2 * (t : ℝ) ^ (R * j) * Real.exp (-(t : ℝ)) +
        ((j + 3 : ℕ) : ℝ) * 2 ^ (3 * j + 6) * (t : ℝ) ^ (R * (3 * j + 6)) * (1 / 2 : ℝ) ^ t < 1 := by
  have hfirst := polynomial_exp_neg_mul_tendsToZero 2 1 (R * j) (by norm_num)
  have hsecond := (tendsto_pow_const_mul_const_pow_of_lt_one (R * (3 * j + 6))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
    (((j + 3 : ℕ) : ℝ) * 2 ^ (3 * j + 6))
  have hlim : Tendsto (fun t : ℕ ↦ 2 * (t : ℝ) ^ (R * j) * Real.exp (-(t : ℝ)) +
      ((j + 3 : ℕ) : ℝ) * 2 ^ (3 * j + 6) * (t : ℝ) ^ (R * (3 * j + 6)) * (1 / 2 : ℝ) ^ t)
      atTop (𝓝 0) := by
    simpa only [one_mul, neg_one_mul, zero_add, mul_zero, mul_assoc] using hfirst.add hsecond
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  exact ⟨max T 1, le_max_right _ _, fun t ht ↦ hT t ((le_max_left _ _).trans ht)⟩

end Erdos207
