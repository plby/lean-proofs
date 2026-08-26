/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Dominated convergence for the averaged small Gaussian interval.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.GaussianIntervals

namespace Erdos521

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem standardGaussianInterval_quotient_norm_le {α : ℝ} (hα : 0 < α) (y : ℝ) :
    ‖standardGaussianInterval (α * |y|) / α‖ ≤ gaussianPDFReal 0 1 0 * |y| := by
  have ht : 0 ≤ α * |y| := mul_nonneg hα.le (abs_nonneg y)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (standardGaussianInterval_nonneg ht) hα.le)]
  apply (div_le_iff₀ hα).mpr
  have h := standardGaussianInterval_le ht
  nlinarith

theorem standardGaussian_density_mul_abs_moment :
    (∫ y : ℝ, gaussianPDFReal 0 1 0 * |y| ∂gaussianReal 0 1) = 1 / Real.pi := by
  rw [integral_const_mul, integral_standardGaussian_abs, standardGaussian_density]
  simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, mul_one]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * (2 / Real.sqrt (2 * Real.pi)) =
        2 / (Real.sqrt (2 * Real.pi)) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]; field_simp

theorem averaged_standardGaussianInterval_slope :
    Tendsto (fun α : ℝ ↦ (∫ y : ℝ, standardGaussianInterval (α * |y|) ∂gaussianReal 0 1) / α)
      (𝓝[>] 0) (𝓝 (1 / Real.pi)) := by
  have hmeas : ∀ᶠ α : ℝ in 𝓝[>] 0, AEStronglyMeasurable
      (fun y : ℝ ↦ standardGaussianInterval (α * |y|) / α) (gaussianReal 0 1) :=
    Eventually.of_forall (fun α ↦ ((continuous_standardGaussianInterval.comp
      (continuous_const.mul continuous_abs)).div_const α).aestronglyMeasurable)
  have hbound : ∀ᶠ α : ℝ in 𝓝[>] 0, ∀ᵐ y ∂gaussianReal 0 1,
      ‖standardGaussianInterval (α * |y|) / α‖ ≤ gaussianPDFReal 0 1 0 * |y| := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    exact Eventually.of_forall (standardGaussianInterval_quotient_norm_le hα)
  have hint : Integrable (fun y : ℝ ↦ gaussianPDFReal 0 1 0 * |y|) (gaussianReal 0 1) :=
    (IsGaussian.integrable_id (μ := gaussianReal 0 1)).abs.const_mul _
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun y : ℝ ↦ gaussianPDFReal 0 1 0 * |y|) hmeas hbound hint
    (Eventually.of_forall standardGaussianInterval_scaled_slope)
  rw [standardGaussian_density_mul_abs_moment] at h
  simpa only [integral_div] using h

end Erdos521
