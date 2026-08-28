import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbar

/-!
# Holomorphic parameters of the partial Cauchy–Green operator

The smoothness of the integral is not used as a substitute for complex
analyticity.  The proved commutation with the parameter `∂̄` derivative
and the one-variable Cauchy–Riemann theorem give actual analytic parameter
slices on any prescribed open set.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open HolomorphicCousin

@[simp] theorem cauchySecond_zero : cauchySecond (0 : ℂ × ℂ → ℂ) = 0 := by
  funext q
  simp [cauchySecond, cauchyGreen]

/-- Vanishing of the parameter antiholomorphic derivative is preserved by the
actual integral in the second variable. -/
theorem dbarFirst_cauchySecond_eq_zero {f : ℂ × ℂ → ℂ} {k U : Set ℂ}
    (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ z w, w ∉ k → f (z, w) = 0)
    (hd : ∀ z ∈ U, ∀ w, dbarFirst f (z, w) = 0)
    {z : ℂ} (hz : z ∈ U) (w : ℂ) :
    dbarFirst (cauchySecond f) (z, w) = 0 := by
  rw [dbarFirst_cauchySecond hf hk hfk]
  simp only [cauchySecond, cauchyGreen, hd z hz, mul_zero, integral_zero]

/-- Holomorphic dependence on an independent complex parameter passes through
the convergent Cauchy–Green integral. -/
theorem analyticOnNhd_cauchySecond_parameter {f : ℂ × ℂ → ℂ} {k U : Set ℂ}
    (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ z w, w ∉ k → f (z, w) = 0) (hU : IsOpen U)
    (hh : ∀ w, AnalyticOnNhd ℂ (fun z => f (z, w)) U) (w : ℂ) :
    AnalyticOnNhd ℂ (fun z => cauchySecond f (z, w)) U := by
  apply analyticOnNhd_of_dbar_eq_zero hU
  · exact (((contDiff_cauchySecond hf hk hfk).comp
      (contDiff_prodMk_left w)).differentiable one_ne_zero).differentiableOn
  · intro z hz
    exact dbarFirst_cauchySecond_eq_zero hf hk hfk
      (fun z hz w => dbar_eq_zero_of_differentiableAt ((hh w z hz).differentiableAt))
      hz w

/-- A zero slice gives a zero slice of the actual integral; this statement
requires no regularity or convergence assumptions. -/
theorem cauchySecond_eq_zero_of_slice_eq_zero {f : ℂ × ℂ → ℂ} {z : ℂ}
    (hf : ∀ w, f (z, w) = 0) (w : ℂ) : cauchySecond f (z, w) = 0 := by
  simp only [cauchySecond, cauchyGreen, hf, mul_zero, integral_zero]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
