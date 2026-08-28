import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsCoordinates

/-!
# Vertical derivatives of the original inverse period coordinates

The vertical differential is computed by restricting the genuine jointly
smooth coordinate function to the original fibre and differentiating that
literal restriction. No vertical differential identity is assumed.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- The actual real-linear coordinate functional on the original covering
plane, obtained from the inverse period map. -/
def verticalCoordinateLinear (b : U) (j : Fin 4) : ComplexPlane₂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j).comp
    (P.periodEquiv b).symm.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem verticalCoordinateLinear_apply (b : U) (j : Fin 4)
    (w : ComplexPlane₂) :
    verticalCoordinateLinear P b j w = ((P.periodEquiv b).symm w j : ℂ) := rfl

/-- The literal restriction of the full ambient coordinate to a fibre is
the original inverse-period real-linear functional. -/
theorem coordinate_slice_eq (b : U) (j : Fin 4) :
    (fun z : ComplexPlane₂ => coordinate P j ((b : ℂ), z)) =
      verticalCoordinateLinear P b j := by
  funext z
  exact coordinate_apply P j b z

/-- The full real Fréchet derivative on every vertical tangent vector is
the derivative of the actual inverse period map on that fibre. -/
theorem coordinate_fderiv_vertical (j : Fin 4) (b : U) (z w : ComplexPlane₂) :
    fderiv ℝ (coordinate P j) ((b : ℂ), z) (0, w) =
      ((P.periodEquiv b).symm w j : ℂ) := by
  have hAt := coordinate_differentiableAt P j ((b : ℂ), z) b.property
  have hcomp := hAt.hasFDerivAt.comp z
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) (b : ℂ) z)
  change HasFDerivAt (fun y : ComplexPlane₂ => coordinate P j ((b : ℂ), y)) _ z at hcomp
  rw [coordinate_slice_eq] at hcomp
  have h := hcomp.unique (verticalCoordinateLinear P b j).hasFDerivAt
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    verticalCoordinateLinear_apply] using
    congrArg (fun L : ComplexPlane₂ →L[ℝ] ℂ => L w) h

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms
