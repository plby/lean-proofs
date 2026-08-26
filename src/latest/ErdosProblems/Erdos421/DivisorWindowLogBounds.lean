import ErdosProblems.Erdos421.DivisorWindowUniformBound

/-! # Logarithmic factors in the type-I divisor-window estimate -/

namespace Erdos421

theorem divisor_window_frequency_log_le {X : ℝ} (hX : 1 ≤ X) (hlog : 1 ≤ Real.log X)
    {M : ℕ} (hM : (M : ℝ) ≤ X) :
    Real.log (4 * Real.pi * X ^ 4 * M ^ 2 + 2) ≤ 32 * Real.log X := by
  have hXpos : 0 < X := by linarith
  have hM2 : (M : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg M) hM 2
  have hX6 : (1 : ℝ) ≤ X ^ 6 := one_le_pow₀ hX
  have harg : 4 * Real.pi * X ^ 4 * M ^ 2 + 2 ≤ (4 * Real.pi + 2) * X ^ 6 := by
    have hb := mul_le_mul_of_nonneg_left hM2 (by positivity : 0 ≤ 4 * Real.pi * X ^ 4)
    nlinarith
  have hb := Real.log_le_log (by positivity : 0 < 4 * Real.pi * X ^ 4 * M ^ 2 + 2) harg
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hb
  norm_num at hb
  have hc := Real.log_le_sub_one_of_pos (by positivity : 0 < 4 * Real.pi + 2)
  nlinarith [Real.pi_lt_four]

theorem divisor_window_harmonic_le {X : ℝ} (hlog : 1 ≤ Real.log X)
    {M : ℕ} (hM : (M : ℝ) ≤ X) : (harmonic M : ℝ) ≤ 2 * Real.log X := by
  by_cases hM0 : M = 0
  · subst M
    simp only [harmonic_zero, Rat.cast_zero]
    linarith
  have hMp : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM0
  have hl := Real.log_le_log hMp hM
  have hb := harmonic_le_one_add_log M
  linarith

end Erdos421
