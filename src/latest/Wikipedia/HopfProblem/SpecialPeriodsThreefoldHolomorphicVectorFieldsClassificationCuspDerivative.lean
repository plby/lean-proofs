import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspReferencePullback
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspComparison
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspComparisonDerivative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspAxes

/-!
# The native tangent comparison at the filled cusp

The exact map square between the reference toric chart, its logarithmic
cover, and the original regular period cover gives an equality of genuine
manifold derivatives. On vertical vectors the base-width scaling is the
identity.
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

/-- The chain rule applied to the actual global comparison square. -/
theorem cuspReference_regular_derivative (x : LogDomain) (u : EL) :
    mfderiv I₃ IL referenceMap (refExpInto x) (refExpDerivative x.val u) =
      mfderiv IL IL HolomorphicForms.RegularCover.globalCover (toRegularCover x)
        (baseWidthLinear u) := by
  have hmap : referenceMap ∘ refExpInto =
      HolomorphicForms.RegularCover.globalCover ∘ toRegularCover :=
    referenceMap_comp_refExpInto.trans globalLogMap_eq_regularCover_comp
  have hd := mfderiv_congr (I := IL) (I' := IL) (x := x) hmap
  rw [mfderiv_comp x (referenceMap_holomorphic.mdifferentiable (by simp) _)
      (refExpInto_holomorphic.mdifferentiable (by simp) x),
    mfderiv_comp x (HolomorphicForms.RegularCover.globalCover_holomorphic.mdifferentiable
      (by simp) _) (toRegularCover_holomorphic.mdifferentiable (by simp) x)] at hd
  have hu := congrArg (fun L : EL →L[ℂ] EL => L u) hd
  change mfderiv I₃ IL referenceMap (refExpInto x)
      (mfderiv IL I₃ refExpInto x u) =
    mfderiv IL IL HolomorphicForms.RegularCover.globalCover (toRegularCover x)
      (mfderiv IL IL toRegularCover x u) at hu
  rw [refExpInto_mfderiv, toRegularCover_mfderiv] at hu
  exact hu

/-- Vertical vectors are unaffected by the actual base-width rescaling. -/
theorem cuspReference_regular_derivative_vertical (x : LogDomain) (u : ComplexPlane₂) :
    mfderiv I₃ IL referenceMap (refExpInto x) (refExpDerivative x.val (0, u)) =
      mfderiv IL IL HolomorphicForms.RegularCover.globalCover (toRegularCover x) (0, u) := by
  simpa only [baseWidthLinear_apply, mul_zero] using
    cuspReference_regular_derivative x (0, u)

/-- The two vertical coordinates on the transverse axis have the exact
normalized exponential factor and no factor of the cusp parameter. -/
theorem cuspRefExpDerivative_vertical_axis
    (s : CuspFamily.LogBase CuspGeometry.data.radius) (u : ComplexPlane₂) (i : Fin 2) :
    refExpDerivative (logPoint s 0).val (0, u) i.succ = K * u i := by
  rw [refExpDerivative_apply]
  fin_cases i <;> simp [logPoint, refExp, smul_eq_mul]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification
