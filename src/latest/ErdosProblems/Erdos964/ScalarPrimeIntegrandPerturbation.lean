import ErdosProblems.Erdos964.ScalarPrimeIntegrand

/-!
# Stability of the scalar prime integrand in the radius parameter
-/

namespace Erdos964

theorem scalarPrimeIntegrand_sub (a b z : ℝ) (hz : z ≠ 0)
    (ha : 1 - a * z ≠ 0) (hb : 1 - b * z ≠ 0) :
    scalarPrimeIntegrand a z - scalarPrimeIntegrand b z =
      scalarSieveFace z * (a - b) / ((1 - a * z) * (1 - b * z)) := by
  unfold scalarPrimeIntegrand
  rw [div_mul_eq_div_div (scalarSieveFace z) z (1 - a * z),
    div_mul_eq_div_div (scalarSieveFace z) z (1 - b * z), div_sub_div _ _ ha hb]
  congr 1
  calc
    _ = (scalarSieveFace z / z * z) * (a - b) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hz]

theorem scalarPrimeIntegrand_parameter_error (a b z d C : ℝ) (hz : z ≠ 0)
    (hd : 0 < d) (ha : d ≤ 1 - a * z) (hb : d ≤ 1 - b * z)
    (hC : |scalarSieveFace z| ≤ C) :
    |scalarPrimeIntegrand a z - scalarPrimeIntegrand b z| ≤ (C / d ^ 2) * |a - b| := by
  have ha0 : 0 < 1 - a * z := hd.trans_le ha
  have hb0 : 0 < 1 - b * z := hd.trans_le hb
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hC
  have hden : d ^ 2 ≤ (1 - a * z) * (1 - b * z) := by
    simpa only [pow_two] using mul_le_mul ha hb hd.le ha0.le
  rw [scalarPrimeIntegrand_sub a b z hz ha0.ne' hb0.ne', abs_div, abs_mul,
    abs_of_pos (mul_pos ha0 hb0)]
  calc
    _ ≤ C * |a - b| / ((1 - a * z) * (1 - b * z)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC (abs_nonneg _)) (by positivity)
    _ ≤ C * |a - b| / d ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hd 2) hden
    _ = _ := by ring

end Erdos964
