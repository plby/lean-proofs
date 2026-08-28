import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quantitative sine bounds for the outer cusp circle

Between one eighth and three eighths of a turn, the sine is strictly
greater than one half.  Reflection gives the corresponding negative bound
between minus three eighths and minus one eighth of a turn.
-/

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp

private theorem sin_two_pi_gt_half_of_le_quarter (t : ℝ) (ht0 : 1 / 8 < t)
    (ht1 : t ≤ 1 / 4) : (1 / 2 : ℝ) < Real.sin (2 * Real.pi * t) := by
  have hlow := mul_lt_mul_of_pos_left ht0 Real.pi_pos
  have hupp := mul_le_mul_of_nonneg_left ht1 Real.pi_pos.le
  calc
    (1 / 2 : ℝ) = Real.sin (Real.pi / 6) := Real.sin_pi_div_six.symm
    _ < Real.sin (2 * Real.pi * t) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      · linarith [Real.pi_pos]
      · linarith
      · linarith [Real.pi_pos]

/-- The sine exceeds one half throughout the indicated open quarter-turn interval. -/
theorem sin_two_pi_gt_half (t : ℝ) (ht0 : 1 / 8 < t) (ht1 : t < 3 / 8) :
    (1 / 2 : ℝ) < Real.sin (2 * Real.pi * t) := by
  by_cases ht : t ≤ 1 / 4
  · exact sin_two_pi_gt_half_of_le_quarter t ht0 ht
  · have h := sin_two_pi_gt_half_of_le_quarter (1 / 2 - t) (by linarith) (by linarith)
    rwa [show 2 * Real.pi * (1 / 2 - t) = Real.pi - 2 * Real.pi * t by ring,
      Real.sin_pi_sub] at h

/-- The sine is below minus one half throughout the reflected open interval. -/
theorem sin_two_pi_lt_neg_half (t : ℝ) (ht0 : -(3 / 8) < t) (ht1 : t < -(1 / 8)) :
    Real.sin (2 * Real.pi * t) < -(1 / 2 : ℝ) := by
  have h := sin_two_pi_gt_half (-t) (by linarith) (by linarith)
  rw [mul_neg, Real.sin_neg] at h
  linarith

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp
