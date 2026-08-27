/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTTotalMainGrowth

/-! # Positive-denominator normalization of the total-weight error -/

namespace Erdos4b.FGKMT

theorem centered_total_relative_error_le {A E S y delta r : ℝ}
    (hS : 0 < S) (hy : 1 ≤ y) (hr : 0 ≤ r) (hd : delta ≤ r)
    (hyr : 1 ≤ y * r) (hE : E ≤ y * S * r)
    (hA : |A - 2 * y * S| ≤ E + ((2 * y + 1) * delta + 1) * S) :
    |A - 2 * y * S| / (2 * y * S) ≤ 3 * r := by
  have hypos : 0 < y := by linarith
  have hcoef : (2 * y + 1) * delta ≤ 3 * y * r := by
    have hfirst := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2 * y + 1)
    have hsecond := mul_le_mul_of_nonneg_right (by linarith : 2 * y + 1 ≤ 3 * y) hr
    exact hfirst.trans hsecond
  have hround : ((2 * y + 1) * delta + 1) * S ≤ 4 * y * S * r := by
    have h := mul_le_mul_of_nonneg_right (add_le_add hcoef hyr) hS.le
    nlinarith
  apply (div_le_iff₀ (by positivity : 0 < 2 * y * S)).mpr
  calc
    _ ≤ E + ((2 * y + 1) * delta + 1) * S := hA
    _ ≤ y * S * r + 4 * y * S * r := add_le_add hE hround
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hypos.le hS.le) hr]

theorem total_main_and_log_power_budget {x S y : ℝ}
    (hx : 1 ≤ x) (hlog : 0 < Real.log x) (hxy : x ≤ y)
    (hS : x ^ (-1 / 4 : ℝ) ≤ S) :
    0 < S ∧ 1 ≤ y * Real.log x ^ (-1 / 4 : ℝ) ∧
      x ^ (1 / 2 : ℝ) ≤ y * S * Real.log x ^ (-1 / 4 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := hxpos.trans_le hxy
  have hSpos : 0 < S := (Real.rpow_pos_of_pos hxpos _).trans_le hS
  have hr : x ^ (-1 / 4 : ℝ) ≤ Real.log x ^ (-1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hlog (Real.log_le_self hxpos.le) (by norm_num)
  have hprod1 : x * x ^ (-1 / 4 : ℝ) = x ^ (3 / 4 : ℝ) := by
    calc
      _ = x ^ (1 : ℝ) * x ^ (-1 / 4 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hxpos]; norm_num
  have hprod2 : x * x ^ (-1 / 4 : ℝ) * x ^ (-1 / 4 : ℝ) = x ^ (1 / 2 : ℝ) := by
    rw [hprod1, ← Real.rpow_add hxpos]
    norm_num
  refine ⟨hSpos, ?_, ?_⟩
  · calc
      _ ≤ x ^ (3 / 4 : ℝ) := Real.one_le_rpow hx (by norm_num)
      _ = x * x ^ (-1 / 4 : ℝ) := hprod1.symm
      _ ≤ _ := mul_le_mul hxy hr (Real.rpow_nonneg hxpos.le _) hypos.le
  · rw [← hprod2]
    exact mul_le_mul
      (mul_le_mul hxy hS (Real.rpow_nonneg hxpos.le _) hypos.le) hr
      (Real.rpow_nonneg hxpos.le _) (mul_nonneg hypos.le hSpos.le)

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.centered_total_relative_error_le
#print axioms Erdos4b.FGKMT.total_main_and_log_power_budget
