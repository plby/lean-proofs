import Mathlib

namespace Erdos327

/-- Certified lower bound for the logarithm used in the odd anatomy tail. -/
theorem log_zo_lower :
    (0.29494314 : ℝ) < Real.log (1.34305 : ℝ) := by
  have h := Real.sum_range_le_log_div
    (x := (34305 / 234305 : ℝ)) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h ⊢
  nlinarith

/-- Certified upper bound for the odd-end mixed-edge weight. -/
theorem log_qo_upper :
    Real.log (1.34288 : ℝ) < (0.29481657 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (x := (34288 / 234288 : ℝ)) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h ⊢
  nlinarith

/-- Certified upper bound for the rough-source mixed-edge weight. -/
theorem log_qb_upper :
    Real.log (2.48933 : ℝ) < (0.912014 : ℝ) := by
  have h := Real.log_div_le_sum_range_add
    (x := (148933 / 348933 : ℝ)) (by norm_num) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at h ⊢
  nlinarith

/-- The source parameter lies below the `3/2` source-saving threshold. -/
theorem source_exponent_lt_three_halves :
    (1.000001 : ℝ) * Real.log 4 < 3 / 2 := by
  rw [Real.log_four_eq]
  nlinarith [Real.log_two_lt_d9]

/-- The odd anatomy moment has a strictly decaying maximal tail. -/
theorem odd_tail_exponent_positive :
    (1.34305 : ℝ) - 1 <
      (1.16312 : ℝ) * Real.log (1.34305 : ℝ) := by
  nlinarith [log_zo_lower]

/-- Odd-host deletions decay faster than the rough density scale. -/
theorem odd_deletion_exponent_gt_one :
    1 < (3.3912 : ℝ) * Real.log (1.34305 : ℝ) := by
  nlinarith [log_zo_lower]

/-- The mixed-edge prefactor grows slower than one power of `log L`. -/
theorem odd_cross_exponent_lt_one :
    (3.3912 : ℝ) * Real.log (1.34288 : ℝ) < 1 := by
  nlinarith [log_qo_upper]

/-- The three-linear-form Euler product has more than one net negative
power of `log L`. -/
theorem cross_exponent_lt_neg_one :
    (1.000001 : ℝ) * Real.log (2.48933 : ℝ)
      + (1.16312 : ℝ) * Real.log (1.34288 : ℝ)
      + (2.48933 : ℝ)⁻¹
      + (1.34288 : ℝ)⁻¹
      + 2 * ((2.48933 : ℝ) * (1.34288 : ℝ))⁻¹
      - 4 < -1 := by
  norm_num at ⊢
  nlinarith [log_qb_upper, log_qo_upper]

end Erdos327
