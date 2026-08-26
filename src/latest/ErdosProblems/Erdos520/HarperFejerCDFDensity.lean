import ErdosProblems.Erdos520.HarperFejer

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory Set
open scoped Interval Pointwise

namespace Erdos
namespace Problem520

/-! # CDF formulas for the scaled Fejér density -/

/-- The CDF of the unscaled Fejér law is the integral of its density. -/
theorem cdf_harperFejerMeasure_eq_integral (x : ℝ) :
    cdf harperFejerMeasure x =
      ∫ y in Iic x, harperFejerDensity y := by
  rw [cdf_eq_real, harperFejerMeasure, measureReal_def,
    withDensity_apply _ measurableSet_Iic]
  refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).symm
  · exact ae_of_all _ fun y ↦ harperFejerDensity_nonneg y
  · exact continuous_harperFejerDensity.measurable.aestronglyMeasurable.restrict

/-- For positive bandwidth, the mapped Fejér law has density
`T * k (T x)`. -/
theorem cdf_harperFejerMeasureScaled_eq_integral
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    cdf (harperFejerMeasureScaled T) x =
      ∫ y in Iic x, T * harperFejerDensity (T * y) := by
  have hpre : (T⁻¹ * ·) ⁻¹' Iic x = Iic (T * x) := by
    ext y
    change T⁻¹ * y ≤ x ↔ y ≤ T * x
    rw [inv_mul_le_iff₀ hT]
  have hmap : cdf (harperFejerMeasureScaled T) x =
      cdf harperFejerMeasure (T * x) := by
    rw [cdf_eq_real, cdf_eq_real, harperFejerMeasureScaled,
      map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre]
  rw [hmap, cdf_harperFejerMeasure_eq_integral]
  have hchange := Measure.setIntegral_comp_smul_of_pos
    (volume : Measure ℝ) harperFejerDensity (Iic x) hT
  simp only [smul_eq_mul, Module.finrank_self, pow_one,
    LinearOrderedField.smul_Iic hT] at hchange
  rw [integral_const_mul, hchange]
  field_simp

/-- The increment of the scaled Fejér CDF is an oriented interval integral
of its scaled density. -/
theorem cdf_harperFejerMeasureScaled_sub_eq_intervalIntegral
    {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    cdf (harperFejerMeasureScaled T) b -
        cdf (harperFejerMeasureScaled T) a =
      ∫ y in a..b, T * harperFejerDensity (T * y) := by
  rw [cdf_harperFejerMeasureScaled_eq_integral hT,
    cdf_harperFejerMeasureScaled_eq_integral hT]
  apply intervalIntegral.integral_Iic_sub_Iic
  · exact (integrable_harperFejerDensity.comp_mul_left' hT.ne').const_mul T |>.integrableOn
  · exact (integrable_harperFejerDensity.comp_mul_left' hT.ne').const_mul T |>.integrableOn

end Problem520
end Erdos
