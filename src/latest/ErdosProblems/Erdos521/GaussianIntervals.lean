/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Small intervals for the standard Gaussian measure.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.GaussianAbsoluteMoment

namespace Erdos521

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

theorem continuous_standardGaussian_density : Continuous (gaussianPDFReal 0 1) := by
  change Continuous (fun x : ℝ ↦ gaussianPDFReal 0 1 x)
  simp_rw [standardGaussian_density]
  fun_prop

theorem standardGaussian_density_le_at_zero (x : ℝ) : gaussianPDFReal 0 1 x ≤ gaussianPDFReal 0 1 0 := by
  rw [standardGaussian_density, standardGaussian_density]
  norm_num
  exact mul_le_of_le_one_right (by positivity)
    (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))

noncomputable def standardGaussianInterval (t : ℝ) : ℝ := ∫ u in 0..t, gaussianPDFReal 0 1 u

theorem standardGaussianInterval_zero : standardGaussianInterval 0 = 0 := by
  simp [standardGaussianInterval]

theorem standardGaussianInterval_hasDerivAt (t : ℝ) :
    HasDerivAt standardGaussianInterval (gaussianPDFReal 0 1 t) t :=
  intervalIntegral.integral_hasDerivAt_right (continuous_standardGaussian_density.intervalIntegrable _ _)
    continuous_standardGaussian_density.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_standardGaussian_density.continuousAt

theorem continuous_standardGaussianInterval : Continuous standardGaussianInterval :=
  continuous_iff_continuousAt.mpr (fun t ↦ (standardGaussianInterval_hasDerivAt t).continuousAt)

theorem standardGaussianInterval_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ standardGaussianInterval t :=
  intervalIntegral.integral_nonneg ht (fun u _ ↦ gaussianPDFReal_nonneg 0 1 u)

theorem standardGaussianInterval_le {t : ℝ} (ht : 0 ≤ t) :
    standardGaussianInterval t ≤ t * gaussianPDFReal 0 1 0 := by
  have h := intervalIntegral.integral_mono_on (μ := volume) ht (continuous_standardGaussian_density.intervalIntegrable _ _)
    (intervalIntegrable_const) (fun u _ ↦ standardGaussian_density_le_at_zero u)
  simpa only [standardGaussianInterval, intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h

theorem standardGaussianInterval_eq_measure {t : ℝ} (ht : 0 ≤ t) :
    standardGaussianInterval t = (gaussianReal 0 1).real (Set.Ioo 0 t) := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun u ↦ gaussianPDFReal_nonneg 0 1 u))]
  rw [standardGaussianInterval, intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]

theorem standardGaussianInterval_scaled_slope (y : ℝ) :
    Tendsto (fun α : ℝ ↦ standardGaussianInterval (α * |y|) / α) (𝓝[>] 0)
      (𝓝 (gaussianPDFReal 0 1 0 * |y|)) := by
  have hd : HasDerivAt (fun α : ℝ ↦ standardGaussianInterval (α * |y|))
      (gaussianPDFReal 0 1 0 * |y|) 0 := by
    simpa only [zero_mul, one_mul, Function.comp_def, id_eq] using
      (standardGaussianInterval_hasDerivAt (0 * |y|)).comp 0 ((hasDerivAt_id 0).mul_const |y|)
  simpa only [zero_add, zero_mul, standardGaussianInterval_zero, sub_zero, smul_eq_mul,
    div_eq_inv_mul] using hd.tendsto_slope_zero_right

end Erdos521
