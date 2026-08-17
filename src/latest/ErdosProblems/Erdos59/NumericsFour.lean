import Mathlib

/-!
# Exact numerical certificate for the four-fold blow-up in Erdős problem 59

The transcendental inequalities in this file are reduced to exact comparisons
of natural-number or rational powers.
-/

namespace Erdos59

/-- The integer-power certificate behind the lower bound on `logb 2 209`. -/
theorem matchings_four_power_certificate : (2 : ℕ) ^ 77 < 209 ^ 10 := by
  norm_num

/-- The exact logarithmic lower bound supplied by `209 ^ 10 > 2 ^ 77`. -/
theorem logb_two_209_gt : (77 : ℝ) / 10 < Real.logb 2 209 := by
  rw [Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 209)]
  rw [← Real.rpow_lt_rpow_iff
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    (by norm_num : (0 : ℝ) ≤ 209) (by norm_num : (0 : ℝ) < 10)]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [Real.rpow_natCast]

/-- The rational cube comparison used to bound `4 ^ (4 / 3)`. -/
theorem twenty_seven_seventeenths_cube_gt_four :
    (4 : ℝ) < ((27 : ℝ) / 17) ^ 3 := by
  norm_num

/-- The exact upper bound `4 ^ (4 / 3) < 108 / 17`. -/
theorem four_rpow_four_thirds_lt :
    (4 : ℝ) ^ ((4 : ℝ) / 3) < (108 : ℝ) / 17 := by
  rw [← Real.rpow_lt_rpow_iff
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
    (by norm_num : (0 : ℝ) ≤ (108 : ℝ) / 17)
    (by norm_num : (0 : ℝ) < 3)]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num [Real.rpow_natCast]

/-- The strict coefficient comparison needed for the four-fold shortcut. -/
theorem numerical_four_certificate :
    ((2669 : ℝ) / 5000) * Real.logb 2 209 >
      ((101 : ℝ) / 100) * ((16 : ℝ) / 25) *
        (4 : ℝ) ^ ((4 : ℝ) / 3) := by
  have hlog := mul_lt_mul_of_pos_left logb_two_209_gt
    (by norm_num : (0 : ℝ) < (2669 : ℝ) / 5000)
  have hrpow := mul_lt_mul_of_pos_left four_rpow_four_thirds_lt
    (by norm_num :
      (0 : ℝ) < ((101 : ℝ) / 100) * ((16 : ℝ) / 25))
  norm_num at hlog hrpow ⊢
  exact hrpow.trans ((by norm_num : (43632 : ℝ) / 10625 < 205513 / 50000).trans hlog)

end Erdos59
