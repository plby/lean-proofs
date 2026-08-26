/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The Gaussian sign-change constant per unit logarithmic spacing.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.GaussianFlipIntegral
import ErdosProblems.Erdos521.GaussianIntervalSlope
import ErdosProblems.Erdos521.LogGaussianSlope

namespace Erdos521

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem gaussian_log_sign_probability_slope :
    Tendsto (fun δ : ℝ ↦ (gaussianPair (logScaleCorrelation δ)).real pairSignFlip / δ)
      (𝓝[>] 0) (𝓝 (1 / (2 * Real.pi))) := by
  have hfirst := averaged_standardGaussianInterval_slope.comp logScaleNoise_tendsto_right
  have hprod := hfirst.mul logScaleNoise_slope
  have heq : (fun δ : ℝ ↦
      ((∫ y : ℝ, standardGaussianInterval (logScaleNoise δ * |y|) ∂gaussianReal 0 1) / logScaleNoise δ) *
        (logScaleNoise δ / δ)) =ᶠ[𝓝[>] 0]
      (fun δ : ℝ ↦ (gaussianPair (logScaleCorrelation δ)).real pairSignFlip / δ) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [gaussianPair_signFlip_integral (logScaleCorrelation_pos δ) (logScaleCorrelation_sq_le_one δ),
      logScaleNoise_eq hδ.le]
    field_simp [(logScaleNoise_pos hδ).ne']
  have hprod' : Tendsto (fun δ : ℝ ↦
      ((∫ y : ℝ, standardGaussianInterval (logScaleNoise δ * |y|) ∂gaussianReal 0 1) / logScaleNoise δ) *
        (logScaleNoise δ / δ)) (𝓝[>] 0) (𝓝 (1 / (2 * Real.pi))) := by
    convert hprod using 1 <;> first | rfl | (congr 1; ring)
  exact hprod'.congr' heq

end Erdos521
