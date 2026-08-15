import Mathlib

open Filter
open scoped Topology

lemma half_quadratic_exponent (n : ℕ) (hn : 8 ≤ n) :
    n + 2 + n / 2 ≤ (n / 2) * (n / 2 + 1) := by
  have hfloor : n ≤ 2 * (n / 2) + 1 := by omega
  have hhalf : 4 ≤ n / 2 := by omega
  nlinarith

lemma scaled_decay_le (n : ℕ) (hn : 8 ≤ n) :
    (2 : ℝ) ^ (n + 2) / (2 : ℝ) ^ ((n / 2) * (n / 2 + 1)) ≤
      ((1 : ℝ) / 2) ^ (n / 2) := by
  rw [one_div_pow]
  apply (div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ ((n / 2) * (n / 2 + 1)))
    (by positivity : 0 < (2 : ℝ) ^ (n / 2))).2
  rw [one_mul, ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (half_quadratic_exponent n hn)

lemma tendsto_half_scaled_decay :
    Tendsto
      (fun n : ℕ ↦
        (2 : ℝ) ^ (n + 2) / (2 : ℝ) ^ ((n / 2) * (n / 2 + 1)))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun n ↦ by positivity)
  · filter_upwards [eventually_ge_atTop 8] with n hn
    exact scaled_decay_le n hn
  · simpa [Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1)).comp
          (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0))

lemma tendsto_half_scaled_decay_zpow :
    Tendsto
      (fun n : ℕ ↦
        (2 : ℝ) ^
          (((n + 2 : ℕ) : ℤ) - (((n / 2) * (n / 2 + 1) : ℕ) : ℤ)))
      atTop (nhds 0) := by
  convert tendsto_half_scaled_decay using 1
  ext n
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]

lemma old_quadratic_exponent (n : ℕ) (hn : 12 ≤ n) :
    2 * n + 3 + n / 2 ≤ (n / 2) * (n / 2 + 1) := by
  have hfloor : n ≤ 2 * (n / 2) + 1 := by omega
  have hhalf : 6 ≤ n / 2 := by omega
  nlinarith

lemma old_scaled_decay_le (n : ℕ) (hn : 12 ≤ n) :
    ((4 : ℝ) / 3) ^ (2 * n + 3) *
        (2 : ℝ) ^ (-(((n / 2) * (n / 2 + 1) : ℕ) : ℤ)) ≤
      ((1 : ℝ) / 2) ^ (n / 2) := by
  rw [zpow_neg, zpow_natCast, inv_eq_one_div, one_div_pow]
  calc
    ((4 : ℝ) / 3) ^ (2 * n + 3) *
          (1 / (2 : ℝ) ^ ((n / 2) * (n / 2 + 1)))
        ≤ (2 : ℝ) ^ (2 * n + 3) *
          (1 / (2 : ℝ) ^ ((n / 2) * (n / 2 + 1))) := by
            gcongr
            norm_num
    _ = (2 : ℝ) ^ (2 * n + 3) /
          (2 : ℝ) ^ ((n / 2) * (n / 2 + 1)) := by ring
    _ ≤ 1 / (2 : ℝ) ^ (n / 2) := by
      apply (div_le_div_iff₀
        (by positivity : 0 < (2 : ℝ) ^ ((n / 2) * (n / 2 + 1)))
        (by positivity : 0 < (2 : ℝ) ^ (n / 2))).2
      rw [one_mul, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (old_quadratic_exponent n hn)

lemma tendsto_old_scaled_decay :
    Tendsto
      (fun n : ℕ ↦
        ((4 : ℝ) / 3) ^ (2 * n + 3) *
          (2 : ℝ) ^ (-(((n / 2) * (n / 2 + 1) : ℕ) : ℤ)))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun n ↦ by positivity)
  · filter_upwards [eventually_ge_atTop 12] with n hn
    exact old_scaled_decay_le n hn
  · simpa [Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1)).comp
          (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0))
