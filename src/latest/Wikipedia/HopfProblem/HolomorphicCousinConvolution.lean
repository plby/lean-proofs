import Wikipedia.HopfProblem.HolomorphicCousinConvolutionKernel
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The compactly supported Cauchy–Green convolution

The inverse kernel is locally integrable in the real plane. Convolving it
with compactly supported smooth data therefore gives a genuine smooth
function, with derivatives obtained by differentiating the data.
-/

noncomputable section

open Complex MeasureTheory
open scoped Convolution

namespace Wikipedia.HopfProblem.HolomorphicCousin

/-- The Cauchy–Green operator defined by its actual plane integral. -/
def cauchyGreen (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / (Real.pi : ℂ)) * ∫ w : ℂ, w⁻¹ * f (z - w)

/-- The defining integral converges for continuous compactly supported data. -/
theorem integrable_cauchyGreen {f : ℂ → ℂ} (hf : Continuous f)
    (hcf : HasCompactSupport f) (z : ℂ) :
    Integrable (fun w : ℂ => w⁻¹ * f (z - w)) :=
  hcf.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_complex_inv hf z

/-- The normalized integral is a convolution for real-bilinear complex multiplication. -/
theorem cauchyGreen_eq_convolution (f : ℂ → ℂ) (z : ℂ) :
    cauchyGreen f z = (1 / (Real.pi : ℂ)) *
      ((fun w : ℂ => w⁻¹) ⋆[ContinuousLinearMap.mul ℝ ℂ] f) z := rfl

/-- The Cauchy–Green operator preserves every finite or smooth differentiability class. -/
theorem contDiff_cauchyGreen {n : ℕ∞} {f : ℂ → ℂ} (hf : ContDiff ℝ n f)
    (hcf : HasCompactSupport f) : ContDiff ℝ n (cauchyGreen f) := by
  change ContDiff ℝ n (fun z => (1 / (Real.pi : ℂ)) *
    ((fun w : ℂ => w⁻¹) ⋆[ContinuousLinearMap.mul ℝ ℂ] f) z)
  exact contDiff_const.mul (hcf.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_complex_inv hf)

/-- The actual real derivative of the Cauchy–Green integral. -/
theorem hasFDerivAt_cauchyGreen {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z : ℂ) :
    HasFDerivAt (cauchyGreen f)
      ((1 / (Real.pi : ℂ)) •
        ((fun w : ℂ => w⁻¹) ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR ℂ]
          fderiv ℝ f) z) z := by
  convert! (hcf.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_complex_inv hf z).const_mul (1 / (Real.pi : ℂ)) using 1

/-- Every directional derivative is obtained by differentiating the compactly supported data. -/
theorem fderiv_cauchyGreen_apply {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z v : ℂ) :
    fderiv ℝ (cauchyGreen f) z v =
      (1 / (Real.pi : ℂ)) * ∫ w : ℂ, w⁻¹ * fderiv ℝ f (z - w) v := by
  rw [(hasFDerivAt_cauchyGreen hf hcf z).fderiv]
  simp only [smul_apply, smul_eq_mul]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_complex_inv (hcf.fderiv ℝ) (hf.continuous_fderiv one_ne_zero)]
  rfl

/-- The differentiated integrand remains integrable in every fixed direction. -/
theorem integrable_cauchyGreen_fderiv {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z v : ℂ) :
    Integrable (fun w : ℂ => w⁻¹ * fderiv ℝ f (z - w) v) :=
  integrable_cauchyGreen
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    (hcf.fderiv_apply ℝ v) z

end Wikipedia.HopfProblem.HolomorphicCousin
