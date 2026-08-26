import ErdosProblems.Erdos421.PerronShiftWidth

/-! # Power and height factors after choosing the Perron contour -/

namespace Erdos421

theorem perronShiftWidth_power_saving {x T : ℝ} (hx : 2 ≤ x) (hT : 1 < T)
    (K : ℕ) (hupper : T ≤ x ^ K) :
    x ^ (1 - perronShiftWidth T) ≤
      x * Real.exp (-perronWidthCoefficient K * (Real.log x) ^ (1 / 16 : ℝ)) := by
  have hxp : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hm := mul_le_mul_of_nonneg_right (perronShiftWidth_lower hx hT K hupper) hlog.le
  rw [perronWidthCoefficient_log_identity K hlog] at hm
  rw [Real.rpow_def_of_pos hxp,
    show Real.log x * (1 - perronShiftWidth T) =
      Real.log x + -(perronShiftWidth T * Real.log x) by ring,
    Real.exp_add, Real.exp_log hxp]
  apply mul_le_mul_of_nonneg_left _ hxp.le
  apply Real.exp_le_exp.mpr
  nlinarith only [hm]

theorem perron_right_power_identity {x : ℝ} (hx : 1 < x) :
    x ^ (1 + 1 / Real.log x) = Real.exp 1 * x := by
  have hxp : 0 < x := by linarith
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [Real.rpow_add hxp, Real.rpow_one, Real.rpow_def_of_pos hxp]
  have he : Real.log x * (1 / Real.log x) = 1 := by field_simp
  rw [he, mul_comm]

theorem perron_height_majorant_le {x T : ℝ} (hx : 2 ≤ x) (hT : 1 < T)
    (K : ℕ) (hupper : T ≤ x ^ K) :
    (2 : ℝ) ^ 52 * (Real.log (T + T / 2)) ^ 2 ≤
      ((2 : ℝ) ^ 52 * ((K : ℝ) + 1) ^ 2) * (Real.log x) ^ 2 := by
  have hlog0 : 0 ≤ Real.log (T + T / 2) := Real.log_nonneg (by linarith)
  have hlogupper : Real.log (T + T / 2) ≤ ((K : ℝ) + 1) * Real.log x :=
    (Real.log_le_log (by linarith : 0 < T + T / 2) (by linarith : T + T / 2 ≤ 2 * T)).trans
      (logarithmic_polynomial_frequency_bound hx (by linarith) K hupper)
  have hp := pow_le_pow_left₀ hlog0 hlogupper 2
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (2 : ℝ) ^ 52)
  exact hm.trans_eq (by ring)

end Erdos421
