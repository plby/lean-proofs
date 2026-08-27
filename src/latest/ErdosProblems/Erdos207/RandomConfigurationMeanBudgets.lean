/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceVortexWellSpread

/-! # Exact power budgets for the source random-configuration probability -/

namespace Erdos207

open scoped NNReal

theorem nnreal_power_ratio_mul_le_of_exponent_le
    (n a : ℝ≥0) (hn : 1 ≤ n) (r s t : ℕ) (hexp : r ≤ s + t) :
    (a / n ^ s) * n ^ r ≤ a * n ^ t := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hnpos _)]
  calc
    _ ≤ a * n ^ (s + t) := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn hexp) zero_le
    _ = _ := by rw [pow_add]; ring

theorem vortexRootExponent_le_three_mul {j r : ℕ} (hr : 1 ≤ r) :
    vortexRootExponent j r ≤ 3 * r := by
  unfold vortexRootExponent
  split_ifs with h
  · omega
  · have hne : r ≠ 1 := fun heq ↦ h (Or.inl heq)
    omega

theorem randomConfiguration_root_exponent_budget
    {j r : ℕ} (hj : 4 ≤ j) (hr : 1 ≤ r) (hrj : r ≤ j - 2) :
    3 * (j - 2 - r) ≤ (2 * j - 6) + (j - vortexRootExponent j r) := by
  have hv := vortexRootExponent_le_three_mul (j := j) hr
  have hvj := vortexRootExponent_le_order hr hrj
  omega

noncomputable def sourceRandomConfigurationProbability (n delta : ℝ≥0) (j : ℕ) : ℝ≥0 :=
  delta / n ^ (2 * j - 6)

theorem sourceRandomConfigurationProbability_le_one
    (n delta : ℝ≥0) (j : ℕ) (hn : 1 ≤ n) (hdelta : 1 ≤ delta)
    (hdeltaSq : delta ^ 2 ≤ n) (hj : 4 ≤ j) : sourceRandomConfigurationProbability n delta j ≤ 1 := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hdeltaN : delta ≤ n := by
    calc
      delta = delta * 1 := (mul_one _).symm
      _ ≤ delta * delta := mul_le_mul_of_nonneg_left hdelta zero_le
      _ = delta ^ 2 := (pow_two _).symm
      _ ≤ n := hdeltaSq
  apply (div_le_one (pow_pos hnpos _)).mpr
  calc
    delta ≤ n := hdeltaN
    _ = n ^ 1 := (pow_one _).symm
    _ ≤ n ^ (2 * j - 6) := pow_le_pow_right₀ hn (by omega)

theorem sourceRandomConfiguration_root_mean_le
    (n delta : ℝ≥0) (j r : ℕ) (hn : 1 ≤ n) (hj : 4 ≤ j) (hr : 1 ≤ r) (hrj : r ≤ j - 2) :
    sourceRandomConfigurationProbability n delta j * (n ^ 3) ^ (j - 2 - r) ≤
      delta * n ^ (j - vortexRootExponent j r) := by
  unfold sourceRandomConfigurationProbability
  rw [← pow_mul]
  exact nnreal_power_ratio_mul_le_of_exponent_le n delta hn _ _ _
    (randomConfiguration_root_exponent_budget hj hr hrj)

theorem sourceRandomConfiguration_pair_mean_le_one
    (n delta : ℝ≥0) (j : ℕ) (hn : 1 ≤ n) (hdeltaSq : delta ^ 2 ≤ n) (hj : 4 ≤ j) :
    (sourceRandomConfigurationProbability n delta j) ^ 2 * (n ^ 3) ^ (j - 3) ≤ 1 := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  unfold sourceRandomConfigurationProbability
  rw [div_pow, ← pow_mul, ← pow_mul, div_mul_eq_mul_div]
  apply (div_le_one (pow_pos hnpos _)).mpr
  calc
    _ ≤ n * n ^ (3 * (j - 3)) := mul_le_mul_of_nonneg_right hdeltaSq zero_le
    _ = n ^ (1 + 3 * (j - 3)) := by rw [pow_add, pow_one]
    _ ≤ _ := pow_le_pow_right₀ hn (by omega)

theorem sourceRandomConfiguration_mixed_mean_le_one
    (n delta y : ℝ≥0) (j : ℕ) (hn : 1 ≤ n) (hdeltaY : delta * y ≤ n) (hj : 4 ≤ j) :
    sourceRandomConfigurationProbability n delta j * y * n ^ (j - 3) ≤ 1 := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  unfold sourceRandomConfigurationProbability
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_one (pow_pos hnpos _)).mpr
  calc
    _ ≤ n * n ^ (j - 3) := mul_le_mul_of_nonneg_right hdeltaY zero_le
    _ = n ^ (1 + (j - 3)) := by rw [pow_add, pow_one]
    _ ≤ _ := pow_le_pow_right₀ hn (by omega)

theorem sourceRandomConfiguration_order_four_mean_le
    (n delta : ℝ≥0) (hn : 1 ≤ n) :
    sourceRandomConfigurationProbability n delta 4 * n ≤ delta := by
  have h := nnreal_power_ratio_mul_le_of_exponent_le n delta hn 1 2 0 (by omega)
  simpa only [sourceRandomConfigurationProbability, show 2 * 4 - 6 = 2 by omega, pow_one, pow_zero, mul_one] using h

end Erdos207
