import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic

/-! # Explicit inverse-square tails for absolutely convergent integrals -/

namespace Erdos421

open Filter MeasureTheory Set

theorem norm_integral_Ioi_inv_square_le {F : ℝ → ℂ} {H C : ℝ}
    (hH : 0 < H) (hbound : ∀ y : ℝ, H < y → ‖F y‖ ≤ C / y ^ 2) :
    ‖∫ y : ℝ in Ioi H, F y‖ ≤ C / H := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hH).const_mul C
  have hb : ‖∫ y : ℝ in Ioi H, F y‖ ≤ ∫ y : ℝ in Ioi H, C * y ^ (-2 : ℝ) := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hH.trans hy
    have he : y ^ (-2 : ℝ) = 1 / y ^ 2 := by
      rw [Real.rpow_neg hy0.le, Real.rpow_two, one_div]
    simpa only [he, mul_one_div] using hbound y hy
  apply hb.trans_eq
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hH]
  norm_num [Real.rpow_neg_one, div_eq_mul_inv]

theorem norm_integral_Iic_neg_inv_square_le {F : ℝ → ℂ} {H C : ℝ}
    (hH : 0 < H) (hbound : ∀ y : ℝ, y < -H → ‖F y‖ ≤ C / y ^ 2) :
    ‖∫ y : ℝ in Iic (-H), F y‖ ≤ C / H := by
  rw [← integral_comp_neg_Ioi H F]
  apply norm_integral_Ioi_inv_square_le hH
  intro y hy
  simpa only [neg_sq] using hbound (-y) (by linarith)

theorem integral_sub_symmetric_interval_eq_tails {F : ℝ → ℂ} (hF : Integrable F) (H : ℝ) :
    (∫ y : ℝ, F y) - (∫ y : ℝ in -H..H, F y) =
      (∫ y : ℝ in Iic (-H), F y) + (∫ y : ℝ in Ioi H, F y) := by
  have hpart := intervalIntegral.integral_Iic_add_Ioi (b := H) hF.integrableOn hF.integrableOn
  have hmid := intervalIntegral.integral_Iic_sub_Iic (a := -H) (b := H)
    hF.integrableOn hF.integrableOn
  rw [← hpart, ← hmid]
  abel

theorem norm_integral_sub_symmetric_interval_le {F : ℝ → ℂ} {H C : ℝ}
    (hF : Integrable F) (hH : 0 < H)
    (hbound : ∀ y : ℝ, H < |y| → ‖F y‖ ≤ C / y ^ 2) :
    ‖(∫ y : ℝ, F y) - (∫ y : ℝ in -H..H, F y)‖ ≤ 2 * C / H := by
  have hright := norm_integral_Ioi_inv_square_le hH (fun y hy ↦
    hbound y (by rwa [abs_of_pos (hH.trans hy)]))
  have hleft := norm_integral_Iic_neg_inv_square_le hH (fun y hy ↦
    hbound y (by rw [abs_of_neg (by linarith : y < 0)]; linarith))
  rw [integral_sub_symmetric_interval_eq_tails hF H]
  have h := (norm_add_le _ _).trans (add_le_add hleft hright)
  exact h.trans_eq (by ring)

end Erdos421
