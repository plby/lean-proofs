import Arxiv.Arxiv2411_18291.FiniteModularErrorBudget

/-!
# An explicit modular-generator threshold for every modulus

Here r is the face rank. The additional power pays for the modulus in the
saturation estimate. For moduli through the decoder modulus the threshold
is exactly the existing paper threshold.
-/

namespace Arxiv2411_18291

def correctedModularGeneratorThreshold (q r N : ℕ) : ℕ :=
  max (paperSizeThreshold q (r + 1))
    ((max 1 (256 * q.choose (r + 1) * q.choose r * N)) ^
      (10 * paperInverseAlpha q (r + 1)))

theorem modular_generator_threshold_exponent {q r : ℕ} (hqr : r + 1 < q) :
    ((10 * paperInverseAlpha q (r + 1) : ℕ) : ℝ) *
      (paperAlpha q (r + 1) / 10) = 1 := by
  push_cast
  calc
    _ = paperAlpha q (r + 1) * paperInverseAlpha q (r + 1) := by ring
    _ = 1 := paperAlpha_mul_inverse hqr

theorem paperThreshold_le_modularGeneratorThreshold (q r N : ℕ) :
    paperSizeThreshold q (r + 1) ≤ correctedModularGeneratorThreshold q r N :=
  le_max_left _ _

theorem modular_generator_margin_of_threshold {q r n N : ℕ} (hqr : r + 1 < q)
    (hn : correctedModularGeneratorThreshold q r N ≤ n) :
    (256 * q.choose (r + 1) * q.choose r * N : ℝ) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 10) := by
  let M := max 1 (256 * q.choose (r + 1) * q.choose r * N)
  have hpow : M ^ (10 * paperInverseAlpha q (r + 1)) ≤ n := (le_max_right _ _).trans hn
  have hh := Real.rpow_le_rpow (Nat.cast_nonneg (M ^ (10 * paperInverseAlpha q (r + 1))))
    (by exact_mod_cast hpow : ((M ^ (10 * paperInverseAlpha q (r + 1)) : ℕ) : ℝ) ≤ n)
    (div_nonneg (paperAlpha_pos hqr).le (by norm_num : (0 : ℝ) ≤ 10))
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg M),
    modular_generator_threshold_exponent hqr, Real.rpow_one] at hh
  exact (show (256 * q.choose (r + 1) * q.choose r * N : ℝ) ≤ M by
    exact_mod_cast (le_max_right 1 (256 * q.choose (r + 1) * q.choose r * N))).trans hh

theorem modularGeneratorThreshold_eq_paperThreshold {q r N : ℕ} (hqr : r + 1 < q)
    (hN : N ≤ (r + 1).factorial * q.choose (r + 1)) :
    correctedModularGeneratorThreshold q r N = paperSizeThreshold q (r + 1) := by
  let n := paperSizeThreshold q (r + 1)
  let M := max 1 (256 * q.choose (r + 1) * q.choose r * N)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (paperSizeThreshold_one_lt hqr).le
  have hM : (M : ℝ) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 10) := by
    rw [show (M : ℝ) = max 1 (256 * q.choose (r + 1) * q.choose r * N : ℝ) by
      dsimp only [M]; push_cast; rfl]
    exact max_le (Real.one_le_rpow hn1
      (div_nonneg (paperAlpha_pos hqr).le (by norm_num : (0 : ℝ) ≤ 10)))
      (generator_modulus_margin_paper_threshold hqr le_rfl hN)
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg M) hM
    (10 * paperInverseAlpha q (r + 1))
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n),
    show (paperAlpha q (r + 1) / 10) * ((10 * paperInverseAlpha q (r + 1) : ℕ) : ℝ) = 1 by
      rw [mul_comm]; exact modular_generator_threshold_exponent hqr,
    Real.rpow_one] at hp
  apply max_eq_left
  exact_mod_cast hp

end Arxiv2411_18291
