import ErdosProblems.Erdos964.ScalarHarmonicPowerMean

/-!
# Normalizing logarithmic mean estimates
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

theorem tendsto_log_power_normalized_of_error (F : ℝ → ℝ) (c C : ℝ) (hC : 0 ≤ C)
    (k : ℕ)
    (herror : ∀ x : ℝ, 1 ≤ x →
      |F x - c * (Real.log x) ^ (k + 1)| ≤ C * (1 + Real.log x) ^ k) :
    Tendsto (fun x : ℝ => F x / (Real.log x) ^ (k + 1)) atTop (𝓝 c) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖F x / (Real.log x) ^ (k + 1) - c‖ ≤ C * 2 ^ k / Real.log x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx hlog
    have hlogpos : 0 < Real.log x := zero_lt_one.trans_le hlog
    have hid : F x / (Real.log x) ^ (k + 1) - c =
        (F x - c * (Real.log x) ^ (k + 1)) / (Real.log x) ^ (k + 1) := by
      field_simp
    rw [Real.norm_eq_abs, hid, abs_div, abs_of_pos (pow_pos hlogpos _)]
    calc
      _ ≤ C * (1 + Real.log x) ^ k / (Real.log x) ^ (k + 1) :=
        div_le_div_of_nonneg_right (herror x hx) (by positivity)
      _ ≤ C * (2 * Real.log x) ^ k / (Real.log x) ^ (k + 1) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by linarith) k) hC) (by positivity)
      _ = C * 2 ^ k / Real.log x := by
        rw [mul_pow, pow_succ]
        field_simp
  exact squeeze_zero' (Eventually.of_forall (fun x => norm_nonneg _)) hbound
    (Real.tendsto_log_atTop.const_div_atTop (C * 2 ^ k))

theorem tendsto_coprime_harmonic_power_mean (M : ℕ) (hM : 0 < M) (k : ℕ) :
    Tendsto (fun x : ℝ =>
      abelCumulative (coprimeHarmonicAF M ^ (k + 1) : ArithmeticFunction ℝ) x /
        (Real.log x) ^ (k + 1)) atTop
      (𝓝 (coprimeHarmonicDensity M ^ (k + 1) / (Nat.factorial (k + 1) : ℝ))) := by
  obtain ⟨C, hC, herror⟩ := exists_coprime_harmonic_power_mean_error M hM k
  exact tendsto_log_power_normalized_of_error _ _ C hC k herror

theorem log_power_error_abs_bound (F : ℝ → ℝ) (c C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (x : ℝ) (hx : 1 ≤ x)
    (herror : |F x - c * (Real.log x) ^ (k + 1)| ≤ C * (1 + Real.log x) ^ k) :
    |F x| ≤ (C + |c|) * (1 + Real.log x) ^ (k + 1) := by
  have hlog := Real.log_nonneg hx
  have hbase : 1 ≤ 1 + Real.log x := by linarith
  have hpow1 : (1 + Real.log x) ^ k ≤ (1 + Real.log x) ^ (k + 1) :=
    pow_le_pow_right₀ hbase (by omega)
  have hpow2 : (Real.log x) ^ (k + 1) ≤ (1 + Real.log x) ^ (k + 1) :=
    pow_le_pow_left₀ hlog (by linarith) _
  have h := abs_sub_le (F x) (c * (Real.log x) ^ (k + 1)) 0
  simp only [sub_zero, abs_mul, abs_of_nonneg (pow_nonneg hlog (k + 1))] at h
  nlinarith [mul_le_mul_of_nonneg_left hpow1 hC,
    mul_le_mul_of_nonneg_left hpow2 (abs_nonneg c)]

end Erdos964
