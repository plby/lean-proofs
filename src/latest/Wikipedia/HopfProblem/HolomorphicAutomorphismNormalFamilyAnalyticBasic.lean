import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamilyAnalyticKernels
import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamilyAnalyticIntegral
import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamilyAnalyticCauchy

/-!
# Three-variable analyticity from the actual Cauchy formula

The bounded triple-contour functional applied to the jointly analytic
kernels equals the original differentiable function.  Thus analyticity
is a conclusion, not an additional assumption on that function.
-/

noncomputable section

open Set Metric

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily.AnalyticThreefold

theorem boundaryIntegral_eq_tripleCircleIntegral {f : ProductModel → ℂ} {r : ℝ}
    (hr : 0 < r) (hf : ContinuousOn f (closedCube r))
    {z : ProductModel} (hz : z ∈ openCube r) :
    tripleCircleIntegralCLM r hr (boundaryKernel r (boundaryValues hf) z) =
      ∮ ξ in C(0, r), ∮ η in C(0, r), ∮ ζ in C(0, r),
        (ξ - z.1)⁻¹ * (ζ - z.2.1)⁻¹ * (η - z.2.2)⁻¹ * f (ξ, (ζ, η)) := by
  apply tripleCircleIntegralCLM_apply_restrict r hr
    (boundaryKernel r (boundaryValues hf) z)
    (fun w : ProductModel =>
      (w.1 - z.1)⁻¹ * (w.2.1 - z.2.1)⁻¹ * (w.2.2 - z.2.2)⁻¹ * f w)
  intro ξ ζ η hξ hζ hη
  rw [boundaryKernel_apply _ hz]
  rfl

/-- Complex differentiability on the closed polydisc implies genuine
joint analyticity on its interior. -/
theorem analyticOnNhd_cube_of_differentiableOn {f : ProductModel → ℂ} {r : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (closedCube r)) :
    AnalyticOnNhd ℂ f (openCube r) := by
  have hL := analyticOnNhd_boundaryKernel_functional r (boundaryValues hf.continuousOn)
    (tripleCircleIntegralCLM r hr)
  have hscaled : AnalyticOnNhd ℂ
      (fun z => (2 * Real.pi * Complex.I : ℂ)⁻¹ ^ 3 *
        tripleCircleIntegralCLM r hr (boundaryKernel r (boundaryValues hf.continuousOn) z))
      (openCube r) := analyticOnNhd_const.mul hL
  apply AnalyticOnNhd.congr (isOpen_openCube r) hscaled
  intro z hz
  dsimp only
  rw [boundaryIntegral_eq_tripleCircleIntegral hr hf.continuousOn hz]
  exact tripleCircleIntegral_eq_of_differentiableOn hr hf hz

end Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily.AnalyticThreefold
