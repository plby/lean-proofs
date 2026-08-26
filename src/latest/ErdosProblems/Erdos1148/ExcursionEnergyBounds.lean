import ErdosProblems.Erdos1148.FlowTimeBounds

/-! # Uniform lower bounds at the extended ends of a cusp excursion -/

namespace Erdos1148.DukeArithmetic

lemma energy_coefficient_lower {p R X Y : ℝ} (hp : 0 < p)
    (hprev : R ≤ p * X + Y / p) (hnext : p * Y ≤ R) :
    R * ((p ^ 2 - 1) / p ^ 3) ≤ X := by
  have hY : Y / p ≤ R / p ^ 2 := by
    have hY' : Y ≤ R / p := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hnext)
    calc
      Y / p ≤ (R / p) / p := div_le_div_of_nonneg_right hY' hp.le
      _ = R / p ^ 2 := by ring
  have hbound : R - R / p ^ 2 ≤ X * p := by linarith
  calc
    R * ((p ^ 2 - 1) / p ^ 3) = (R - R / p ^ 2) / p := by field_simp
    _ ≤ X := (div_le_iff₀ hp).mpr hbound

noncomputable def cuspEndpointLengthSqLower : ℝ :=
  ((Real.exp 1) ^ 2 - 1) / (Real.exp 1) ^ 3

lemma cuspEndpointLengthSqLower_pos : 0 < cuspEndpointLengthSqLower := by
  have hp : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  unfold cuspEndpointLengthSqLower
  apply div_pos _ (pow_pos (Real.exp_pos _) 3)
  nlinarith

lemma cuspEndpointLengthSqLower_le_one : cuspEndpointLengthSqLower ≤ 1 := by
  have hp : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  unfold cuspEndpointLengthSqLower
  apply (div_le_one (pow_pos (Real.exp_pos _) 3)).mpr
  nlinarith [mul_nonneg (by linarith : 0 ≤ Real.exp (1 : ℝ) - 1)
    (sq_nonneg (Real.exp (1 : ℝ)))]

lemma exponential_energy_initial_coefficient_lower {R X Y L : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hL : 1 ≤ L)
    (hprev : R ≤ Real.exp 1 * X + Real.exp (-1) * Y)
    (hnext : Real.exp (-L) * X + Real.exp L * Y ≤ R) :
    R * cuspEndpointLengthSqLower ≤ X := by
  have hYnext : Real.exp 1 * Y ≤ R := by
    calc
      _ ≤ Real.exp L * Y := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hL) hY
      _ ≤ R := by nlinarith [mul_nonneg (Real.exp_pos (-L)).le hX]
  apply energy_coefficient_lower (Real.exp_pos (1 : ℝ)) (hnext := hYnext)
  simpa only [Real.exp_neg, div_eq_mul_inv, mul_comm] using hprev

end Erdos1148.DukeArithmetic
