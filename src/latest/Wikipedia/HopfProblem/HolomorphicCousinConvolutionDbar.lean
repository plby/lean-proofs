import Wikipedia.HopfProblem.HolomorphicCousinConvolution
import Wikipedia.HopfProblem.HolomorphicCousinWirtinger

/-!
# Passing the antiholomorphic derivative through Cauchy–Green convolution

The derivative is computed using the real-bilinear convolution theorem and
the continuous real-linear functional defining the antiholomorphic part.
No fundamental-solution identity is assumed here.
-/

noncomputable section

open Complex MeasureTheory
open scoped Convolution

namespace Wikipedia.HopfProblem.HolomorphicCousin

/-- The antiholomorphic part commutes with complex multiplication of a differential. -/
theorem dbarLinear_precompR_mul (a : ℂ) (L : ℂ →L[ℝ] ℂ) :
    dbarLinear ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ a L) =
      a * dbarLinear L := by
  change dbarLinear (a • L) = a * dbarLinear L
  exact dbarLinear_complex_smul a L

/-- The antiholomorphic derivative passes through the convergent Cauchy–Green integral. -/
theorem dbar_cauchyGreen_eq_cauchyGreen_dbar {f : ℂ → ℂ}
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) (z : ℂ) :
    dbar (cauchyGreen f) z = cauchyGreen (dbar f) z := by
  have hi : Integrable (fun w : ℂ =>
      (ContinuousLinearMap.mul ℝ ℂ).precompR ℂ w⁻¹ (fderiv ℝ f (z - w))) :=
    (hcf.fderiv ℝ).convolutionExists_right ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ)
      locallyIntegrable_complex_inv (hf.continuous_fderiv one_ne_zero) z
  rw [dbar_eq_dbarLinear, (hasFDerivAt_cauchyGreen hf hcf z).fderiv,
    dbarLinear_complex_smul, convolution_def, ← dbarLinear.integral_comp_comm hi]
  simp only [dbarLinear_precompR_mul, ← dbar_eq_dbarLinear, cauchyGreen]

/-- Explicit integral form of differentiation by `∂̄`. -/
theorem dbar_cauchyGreen_integral {f : ℂ → ℂ}
    (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) (z : ℂ) :
    dbar (cauchyGreen f) z =
      (1 / (Real.pi : ℂ)) * ∫ w : ℂ, w⁻¹ * dbar f (z - w) :=
  dbar_cauchyGreen_eq_cauchyGreen_dbar hf hcf z

end Wikipedia.HopfProblem.HolomorphicCousin
