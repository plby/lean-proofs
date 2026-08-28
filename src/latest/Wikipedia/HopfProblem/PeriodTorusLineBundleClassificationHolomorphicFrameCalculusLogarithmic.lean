import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrameCalculusLocal
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrameCalculusOperations

/-!
# The genuine local logarithmic antiholomorphic derivative is closed

For any actual smooth scalar function nonzero at a point, the quotients
`(∂̄ᵢ f) / f` are smooth there and satisfy the mixed closedness equation.
The equation follows from the proved quotient rule and real Schwarz
commutation; it is not an input to the logarithmic construction.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame

open PeriodTorusLineBundleClassification

/-- The actual logarithmic derivative is smooth at a nonzero smooth point. -/
theorem contDiffAt_logarithmicDbar {f : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (hf : ContDiffAt ℝ ∞ f z) (hne : f z ≠ 0) (i : Fin 2) :
    ContDiffAt ℝ ∞ (fun x => dbarCoordinate f i x / f x) z := by
  simpa only [div_eq_mul_inv] using
    (contDiffAt_dbarCoordinate hf i).mul (hf.fun_inv hne)

/-- The local logarithmic `∂̄` form is genuinely closed. -/
theorem dbar_logarithmic_closed {f : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (hf : ContDiffAt ℝ ∞ f z) (hne : f z ≠ 0) :
    dbarCoordinate (fun x => dbarCoordinate f 1 x / f x) 0 z =
      dbarCoordinate (fun x => dbarCoordinate f 0 x / f x) 1 z := by
  have hfd : DifferentiableAt ℝ f z := hf.differentiableAt (by simp)
  have h₀ : DifferentiableAt ℝ (dbarCoordinate f 0) z :=
    (contDiffAt_dbarCoordinate hf 0).differentiableAt (by simp)
  have h₁ : DifferentiableAt ℝ (dbarCoordinate f 1) z :=
    (contDiffAt_dbarCoordinate hf 1).differentiableAt (by simp)
  rw [dbarCoordinate_div h₁ hfd hne, dbarCoordinate_div h₀ hfd hne,
    dbarCoordinate_zero_one_commute_of_contDiffAt hf]
  ring

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame
