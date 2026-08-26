import ErdosProblems.Erdos421.LogTaylorCoefficients
import ErdosProblems.Erdos421.ReciprocalDifferences
import ErdosProblems.Erdos421.TorusBoxes

/-! # Explicit spacing of logarithmic Taylor coefficients -/

namespace Erdos421

theorem reciprocal_power_drop_lower (j : ℕ) {x y B : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hyB : y ≤ B) :
    (((j + 1 : ℕ) : ℝ) * (y - x)) / B ^ (j + 2) ≤
      1 / x ^ (j + 1) - 1 / y ^ (j + 1) := by
  have h := (reciprocalDifference_bounds j [y - x]
    (by simpa only [List.mem_singleton, forall_eq] using sub_nonneg.mpr hxy) hx).1
  have hy : 0 < y := hx.trans_le hxy
  have hbase : (((j + 1 : ℕ) : ℝ) * (y - x)) / y ^ (j + 2) ≤
      1 / x ^ (j + 1) - 1 / y ^ (j + 1) := by
    simpa only [differenceCoefficient, List.length_singleton, List.prod_singleton,
      List.sum_singleton, reciprocalDifference, iteratedDifference, Nat.ascFactorial_succ,
      Nat.ascFactorial_zero, Nat.add_zero, Nat.mul_one, Nat.add_assoc,
      show x + (y - x) = y by ring]
      using h
  exact (div_le_div_of_nonneg_left (by positivity) (pow_pos hy _)
    (pow_le_pow_left₀ hy.le hyB _)).trans hbase

theorem logTaylorCoefficients_abs {k : ℕ} (j : Fin k) (t : ℝ) {z : ℝ} (hz : 0 < z) :
    |logTaylorCoefficients k t z j| =
      |t| / (2 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) * z ^ ((j : ℕ) + 1)) := by
  unfold logTaylorCoefficients
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : 0 < 2 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) *
      z ^ ((j : ℕ) + 1))]

theorem logTaylorCoefficients_abs_le_quarter {k : ℕ} (j : Fin k) {t A z : ℝ}
    (hA : 0 < A) (hAz : A ≤ z) (ht : |t| ≤ A ^ ((j : ℕ) + 1)) :
    |logTaylorCoefficients k t z j| ≤ 1 / 4 := by
  have hz : 0 < z := hA.trans_le hAz
  have hj : (1 : ℝ) ≤ (((j : ℕ) + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (j : ℕ)
  have hden : 4 ≤ 2 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) := by
    nlinarith [Real.two_le_pi]
  rw [logTaylorCoefficients_abs j t hz]
  calc
    _ ≤ A ^ ((j : ℕ) + 1) /
        (2 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) * z ^ ((j : ℕ) + 1)) :=
      div_le_div_of_nonneg_right ht (by positivity)
    _ ≤ A ^ ((j : ℕ) + 1) /
        (2 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) * A ^ ((j : ℕ) + 1)) :=
      div_le_div_of_nonneg_left (pow_nonneg hA.le _) (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA.le hAz _) (by positivity))
    _ = 1 / (2 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ)) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden

theorem logTaylorCoefficients_span {k : ℕ} (j : Fin k) {t A x y : ℝ}
    (hA : 0 < A) (hAx : A ≤ x) (hAy : A ≤ y) (ht : |t| ≤ A ^ ((j : ℕ) + 1)) :
    |logTaylorCoefficients k t x j - logTaylorCoefficients k t y j| ≤ 1 / 2 := by
  have hx := logTaylorCoefficients_abs_le_quarter j hA hAx ht
  have hy := logTaylorCoefficients_abs_le_quarter j hA hAy ht
  exact (abs_sub _ _).trans (by linarith)

theorem logTaylorCoefficients_difference_abs {k : ℕ} (j : Fin k) (t : ℝ)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    |logTaylorCoefficients k t x j - logTaylorCoefficients k t y j| =
      (|t| / (2 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ))) *
        (1 / x ^ ((j : ℕ) + 1) - 1 / y ^ ((j : ℕ) + 1)) := by
  have hy : 0 < y := hx.trans_le hxy
  have hj : (0 : ℝ) < (((j : ℕ) + 1 : ℕ) : ℝ) := by positivity
  have heq : logTaylorCoefficients k t x j - logTaylorCoefficients k t y j =
      ((-1 : ℝ) ^ (j : ℕ) * t / (2 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ))) *
        (1 / x ^ ((j : ℕ) + 1) - 1 / y ^ ((j : ℕ) + 1)) := by
    unfold logTaylorCoefficients
    field_simp
  have hdrop : 0 ≤ 1 / x ^ ((j : ℕ) + 1) - 1 / y ^ ((j : ℕ) + 1) :=
    sub_nonneg.mpr (div_le_div_of_nonneg_left (by norm_num) (pow_pos hx _)
      (pow_le_pow_left₀ hx.le hxy _))
  rw [heq, abs_mul, abs_of_nonneg hdrop, abs_div, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : 0 < 2 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ))]

theorem logTaylorCoefficients_separation {k : ℕ} (j : Fin k) (t : ℝ)
    {x y B : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hyB : y ≤ B) :
    (|t| / (2 * Real.pi * B ^ ((j : ℕ) + 2))) * (y - x) ≤
      |logTaylorCoefficients k t x j - logTaylorCoefficients k t y j| := by
  have hB : 0 < B := (hx.trans_le hxy).trans_le hyB
  have hj : (0 : ℝ) < (((j : ℕ) + 1 : ℕ) : ℝ) := by positivity
  rw [logTaylorCoefficients_difference_abs j t hx hxy]
  calc
    _ = (|t| / (2 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ))) *
        ((((j : ℕ) + 1 : ℕ) : ℝ) * (y - x) / B ^ ((j : ℕ) + 2)) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_power_drop_lower (j : ℕ) hx hxy hyB)
      (by positivity)

end Erdos421
