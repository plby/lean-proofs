import ErdosProblems.Erdos633b.SharedAngleMetric

/-! Exact real roots and polynomial side coordinates for the pi/8 right tile. -/

namespace Erdos633b

theorem eighth_sine_sq : Real.sin (Real.pi / 8) ^ 2 = (2 - Real.sqrt 2) / 4 := by
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs := Real.sqrt_nonneg (2 : ℝ)
  have hp : 0 ≤ 2 - Real.sqrt 2 := by nlinarith
  rw [Real.sin_pi_div_eight, div_pow, Real.sq_sqrt hp]
  norm_num

theorem eighth_cosine_sq : Real.cos (Real.pi / 8) ^ 2 = (2 + Real.sqrt 2) / 4 := by
  rw [Real.cos_pi_div_eight, div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 + Real.sqrt 2)]
  norm_num

theorem eighth_sine_quartic : (2 * Real.sin (Real.pi / 8)) ^ 4 -
    4 * (2 * Real.sin (Real.pi / 8)) ^ 2 + 2 = 0 := by
  have he : 4 * Real.sin (Real.pi / 8) ^ 2 - 2 = -Real.sqrt 2 := by
    linarith [eighth_sine_sq]
  have hs := congrArg (fun x : ℝ => x ^ 2) he
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem eighth_cosine_quartic : (2 * Real.cos (Real.pi / 8)) ^ 4 -
    4 * (2 * Real.cos (Real.pi / 8)) ^ 2 + 2 = 0 := by
  have he : 4 * Real.cos (Real.pi / 8) ^ 2 - 2 = Real.sqrt 2 := by
    linarith [eighth_cosine_sq]
  have hs := congrArg (fun x : ℝ => x ^ 2) he
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem eighth_cosine_parameter_gt_two : 2 < (2 * Real.cos (Real.pi / 8)) ^ 2 := by
  have hp : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [eighth_cosine_sq]

theorem eighth_sine_parameter_complement :
    2 - (2 * Real.sin (Real.pi / 8)) ^ 2 = Real.sqrt 2 := by
  nlinarith [eighth_sine_sq]

theorem eighth_cosine_polynomial : Real.cos (Real.pi / 8) =
    (3 * (2 * Real.sin (Real.pi / 8)) - (2 * Real.sin (Real.pi / 8)) ^ 3) / 2 := by
  have h := sin_three_mul_eq (Real.pi / 8)
  rw [show 3 * (Real.pi / 8) = Real.pi / 2 - Real.pi / 8 by ring,
    Real.sin_pi_div_two_sub] at h
  linear_combination h

end Erdos633b
