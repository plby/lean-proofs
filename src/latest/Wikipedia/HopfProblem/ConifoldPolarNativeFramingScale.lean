import Wikipedia.HopfProblem.ConifoldPolarNativeFramingDefs

/-!
# The explicit radial correction for the chosen standard half-radius tube

The radius-two smoothing has polar three-radius `3/4`.  The standard sphere
normal radius `1/2` has complement three-radius `sqrt 3`.  Their ratio is
retained explicitly, rather than identifying these two radii implicitly.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConifoldPolar.NativeFraming

/-- The literal scale from polar radius `3/4` to standard complement radius `sqrt 3`. -/
def rescalingFactor : ℝ := 4 * Real.sqrt 3 / 3

theorem rescalingFactor_pos : 0 < rescalingFactor := by
  unfold rescalingFactor
  positivity

theorem rescalingFactor_ne_zero : rescalingFactor ≠ 0 := rescalingFactor_pos.ne'

theorem rescalingFactor_mul_three_quarters :
    rescalingFactor * (3 / 4 : ℝ) = Real.sqrt 3 := by
  unfold rescalingFactor
  ring

/-- The original nonzero real homothety as a continuous linear equivalence. -/
def rescaleEquiv : Base ≃L[ℝ] Base :=
  (LinearEquiv.smulOfNeZero ℝ Base rescalingFactor rescalingFactor_ne_zero).toContinuousLinearEquiv

@[simp] theorem rescaleEquiv_apply (b : Base) :
    rescaleEquiv b = rescalingFactor • b := rfl

@[simp] theorem rescaleEquiv_symm_apply (b : Base) :
    rescaleEquiv.symm b = rescalingFactor⁻¹ • b := rfl

theorem rescaleEquiv_norm (b : Base) :
    ‖rescaleEquiv b‖ = rescalingFactor * ‖b‖ := by
  rw [rescaleEquiv_apply, norm_smul, Real.norm_eq_abs, abs_of_pos rescalingFactor_pos]

theorem half_boundaryProductRadius :
    StandardSixSphereCircleModel.boundaryProductRadius (1 / 2 : ℝ) = Real.sqrt 3 := by
  norm_num [StandardSixSphereCircleModel.boundaryProductRadius,
    StandardSixSphereCircleModel.boundaryBaseRadius, Real.sqrt_div]
  ring

theorem half_forward_boundaryPoint (p : StandardBoundary) :
    StandardSixSphereCircleModel.forward
      (StandardSixSphereCircleModel.boundaryPoint (1 / 2) (by norm_num) (by norm_num) p) =
        (Real.sqrt 3 • p.1.val, p.2) := by
  rw [StandardSixSphereCircleModel.forward_boundaryPoint, half_boundaryProductRadius]

end Wikipedia.HopfProblem.ConifoldPolar.NativeFraming
