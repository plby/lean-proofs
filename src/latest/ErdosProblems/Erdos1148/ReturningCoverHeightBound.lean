import ErdosProblems.Erdos1148.QuantitativeReturningCover
import ErdosProblems.Erdos1148.QuantitativeCuspLifts

/-! # Cubic dependence of the returning-cover constant on endpoint height -/

namespace Erdos1148.DukeArithmetic

theorem returning_cover_constant_le_cubic {Y δ : ℝ} (hY : 1 ≤ Y) (hδ : 0 < δ) :
    (((64 * (2 * (Y + 2)) + 3) ^ 2 + 1) *
      (32 / (Real.sqrt ((Y ^ 2)⁻¹) * δ) + 1) * (2 / δ + 1) ^ 2) ≤
      (67601 * (32 / δ + 1) * (2 / δ + 1) ^ 2) * (Y + 1) ^ 3 := by
  have hYpos : 0 < Y := by linarith
  have hfirst : (64 * (2 * (Y + 2)) + 3) ^ 2 + 1 ≤ 67601 * (Y + 1) ^ 2 := by
    nlinarith [sq_nonneg Y]
  have hfrac : 32 / (Real.sqrt ((Y ^ 2)⁻¹) * δ) = (32 / δ) * Y := by
    rw [Real.sqrt_inv, Real.sqrt_sq hYpos.le]
    field_simp
    <;> ring
  have hsecond : 32 / (Real.sqrt ((Y ^ 2)⁻¹) * δ) + 1 ≤ (32 / δ + 1) * (Y + 1) := by
    rw [hfrac]
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 32) hδ.le]
  have hprod := mul_le_mul hfirst hsecond (by positivity) (by positivity)
  calc
    _ ≤ (67601 * (Y + 1) ^ 2 * ((32 / δ + 1) * (Y + 1))) * (2 / δ + 1) ^ 2 :=
      mul_le_mul_of_nonneg_right hprod (sq_nonneg _)
    _ = _ := by ring

end Erdos1148.DukeArithmetic
