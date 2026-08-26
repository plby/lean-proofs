import ErdosProblems.Erdos1148.HorocycleExcursionWidth

/-! # Uniform norm control in a bounded Gauss coordinate box -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma upperTriangularEnergy_le {X E x h : ℝ} (hx : |x| ≤ 1) (hh : 1 / 2 ≤ h) (hh2 : h ≤ 2) :
    (X - x * E) ^ 2 / h ^ 2 + h ^ 2 * E ^ 2 ≤ 8 * X ^ 2 + 12 * E ^ 2 := by
  have hpos : 0 < h := by linarith
  have hxsq : x ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg x) zero_le_one).mpr hx
  have hhsq : h ^ 2 ≤ 4 := by nlinarith
  have hhsqlower : 1 ≤ 4 * h ^ 2 := by nlinarith
  have hcross : (X - x * E) ^ 2 ≤ 2 * X ^ 2 + 2 * E ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hxsq (sq_nonneg E), sq_nonneg (X + x * E)]
  have hdiv : (X - x * E) ^ 2 / h ^ 2 ≤ 4 * (X - x * E) ^ 2 := by
    apply (div_le_iff₀ (pow_pos hpos 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hhsqlower (sq_nonneg (X - x * E))]
  have hlast := mul_le_mul_of_nonneg_right hhsq (sq_nonneg E)
  linarith

theorem modularVectorLengthSq_gauss_le (g : SL(2, ℝ)) (r x h : ℝ)
    (hx : |x| ≤ 1) (hh : 1 / 2 ≤ h) (hh2 : h ≤ 2) (u v : ℤ) :
    modularVectorLengthSq
      (g * unstableHorocycle r * upperTriangularFrame x h (by linarith : h ≠ 0)) u v ≤
        8 * (modularVector g u v).1 ^ 2 +
          12 * ((modularVector g u v).2 - r * (modularVector g u v).1) ^ 2 := by
  rw [modularVectorLengthSq, modularVector_horocycle_upper_first,
    modularVector_horocycle_upper_second, div_pow, mul_pow]
  exact upperTriangularEnergy_le hx hh hh2

theorem gauss_base_first_coordinate_lower (g : SL(2, ℝ)) (r x h S c : ℝ)
    (hx : |x| ≤ 1) (hh : 1 / 2 ≤ h) (hh2 : h ≤ 2) (hc : 0 ≤ c) (u v : ℤ)
    (hlow : c ≤ modularVectorLengthSq
      (g * unstableHorocycle r * upperTriangularFrame x h (by linarith : h ≠ 0)) u v)
    (hreturn : modularVectorLengthSq
      ((g * unstableHorocycle r * upperTriangularFrame x h (by linarith : h ≠ 0)) * diagonalFlow S)
        u v ≤ 1)
    (hsmall : 96 * Real.exp (-S) ≤ c) :
    Real.sqrt c / 4 ≤ |(modularVector g u v).1| := by
  let E : ℝ := (modularVector g u v).2 - r * (modularVector g u v).1
  have herr : |E| ≤ 2 * Real.exp (-(S / 2)) := by
    have hbound := horocycle_parameter_error_le g r x h S 1 (1 / 2) (by norm_num) hh
      (by norm_num) u v (by simpa only [one_pow] using hreturn)
    simpa only [E, one_mul, div_eq_mul_inv, inv_div, div_one, inv_inv, mul_comm] using hbound
  have hEsq : E ^ 2 ≤ 4 * Real.exp (-S) := by
    have hsq := (sq_le_sq₀ (abs_nonneg E) (by positivity : 0 ≤ 2 * Real.exp (-(S / 2)))).mpr herr
    have hexp : Real.exp (-(S / 2)) ^ 2 = Real.exp (-S) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [sq_abs, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, hexp] using hsq
  have henergy := hlow.trans (modularVectorLengthSq_gauss_le g r x h hx hh hh2 u v)
  have hX : c / 16 ≤ (modularVector g u v).1 ^ 2 := by
    change c ≤ 8 * (modularVector g u v).1 ^ 2 + 12 * E ^ 2 at henergy
    nlinarith
  apply (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt c / 4) (abs_nonneg _)).mp
  rw [div_pow, Real.sq_sqrt hc, sq_abs]
  norm_num only [show (4 : ℝ) ^ 2 = 16 by norm_num]
  exact hX

end Erdos1148.DukeArithmetic
