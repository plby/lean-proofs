import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationCuspDerivative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationCuspLift
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationRegular
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspLogCoefficients
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspOrderTransfer

/-!
# The actual regular vector field has analytic cusp germs

The native reference-chart lift agrees, after the exact exponential
Jacobian, with the vertical coefficient on the original regular cover.
Its two coordinates on the filled transverse axis therefore give actual
analytic germs of the two regular vertical components.
-/

open Wikipedia.HopfProblem.ToricCharts Wikipedia.HopfProblem.CuspUniformization
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification

open HolomorphicForms.Cusp

local notation "E₃" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃
local notation "EL" => ℂ × ComplexPlane₂
local notation "IL" => modelWithCornersSelf ℂ EL
local notation "K" => (2 * Real.pi * Complex.I : ℂ)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  HolomorphicForms.RegularCover.coverChartedSpace
  HolomorphicForms.RegularCover.cover_isManifold

/-- The comparison retains the original logarithmic base point and
the original pair of period-vector coordinates. -/
theorem cuspToRegularCover_logPoint (s : CuspFamily.LogBase CuspGeometry.data.radius)
    (ζ : ComplexPlane₂) :
    toRegularCover (logPoint s ζ) = (cuspRegularBase s, ζ) := rfl

/-- Injectivity of the actual reference differential identifies the
lift with the native exponential derivative of the regular vertical vector. -/
theorem cuspReferenceCoefficients_log (v : Threefold.HolomorphicVectorFields.Field)
    (x : LogDomain) :
    cuspReferenceCoefficients v (refExpInto x) =
      refExpDerivative x.val (0, regularVertical v (toRegularCover x).1) := by
  apply ((cuspReferenceMap_isLocalDiffeomorph (refExpInto x)).mfderivToContinuousLinearEquiv
    (by simp)).injective
  let V : Threefold.Space → EL := fun y => v y
  let L : E₃ →L[ℂ] EL := mfderiv I₃ IL referenceMap (refExpInto x)
  let R : EL →L[ℂ] EL :=
    mfderiv IL IL HolomorphicForms.RegularCover.globalCover (toRegularCover x)
  change L (cuspReferenceLift v (refExpInto x)) =
    L (refExpDerivative x.val (0, regularVertical v (toRegularCover x).1))
  have h₁ : L (cuspReferenceLift v (refExpInto x)) = V (referenceMap (refExpInto x)) :=
    cuspReferenceLift_map v _
  have h₂ : V (referenceMap (refExpInto x)) =
      V (HolomorphicForms.RegularCover.globalCover (toRegularCover x)) :=
    congrArg V ((referenceMap_refExpInto x).trans (globalLogMap_eq_regularCover x))
  have h₃ : V (HolomorphicForms.RegularCover.globalCover (toRegularCover x)) =
      R (regularCoefficients v (toRegularCover x)) := (regularLift_map v _).symm
  have h₄ : R (regularCoefficients v (toRegularCover x)) =
      R (0, regularVertical v (toRegularCover x).1) :=
    congrArg R (regularCoefficients_eq v (toRegularCover x).1 (toRegularCover x).2)
  have h₅ : R (0, regularVertical v (toRegularCover x).1) =
      L (refExpDerivative x.val (0, regularVertical v (toRegularCover x).1)) :=
    (cuspReference_regular_derivative_vertical x (regularVertical v (toRegularCover x).1)).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- On the entire genuine logarithmic cusp cover, restriction to the
filled axis recovers each original vertical coefficient exactly. -/
theorem cuspAxisCoefficient_log (v : Threefold.HolomorphicVectorFields.Field)
    (s : CuspFamily.LogBase CuspGeometry.data.radius) (i : Fin 2) :
    cuspAxisCoefficient v i ⟨exponential s, s.property⟩ =
      regularVertical v (cuspRegularBase s) i := by
  have hx : refExpInto (logPoint s 0) =
      axisInclusion 0 ⟨exponential s, s.property⟩ := refExpInto_logAxisPoint 0 s
  change cuspReferenceCoefficients v (axisInclusion 0 ⟨exponential s, s.property⟩)
    i.succ / K = _
  rw [← hx, cuspReferenceCoefficients_log, cuspToRegularCover_logPoint,
    cuspRefExpDerivative_vertical_axis]
  have hK : K ≠ 0 := by simp [Real.pi_ne_zero]
  exact mul_div_cancel_left₀ _ hK

/-- The ambient analytic representative agrees on every actual
logarithmic covering point, without any assumed cusp comparison law. -/
theorem cuspGerm_log (v : Threefold.HolomorphicVectorFields.Field)
    (s : CuspFamily.LogBase CuspGeometry.data.radius) (i : Fin 2) :
    regularVertical v (cuspRegularBase s) i = cuspGerm v i (exponential s) := by
  rw [cuspGerm_of_mem v i s.property]
  exact (cuspAxisCoefficient_log v s i).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification
