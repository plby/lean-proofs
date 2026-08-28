import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedCurve
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedNormal

/-!
# The normal tangent quotient of the literal named curve

The two genuine affine charts on the named global curve identify its
native inclusion derivative with the original cusp-axis derivative.
Consequently the normal space below is the literal quotient by the
tangent range of that curve's native manifold inclusion, with its
original quotient topology.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCurve

open ToricCharts ToricFan

local notation "Model" => ℂ × ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local instance curveOneChartedSpace : ChartedSpace ℂ (Curve 1) := chartedSpace 1
local instance curveOneIsManifold : IsManifold I₁ ω (Curve 1) := isManifold 1

/-- The two actual triangles used by the sphere atlas. -/
def axisTriangle : Bool → Triangle
  | false => ToricSpace.referenceTriangle
  | true => Triangle.upperNeighbour 1

/-- The unchanged two affine maps of the actual named curve. -/
def affineMap (b : Bool) : ℂ → Curve 1 := (charts 1).affineMap b

theorem affineMap_val (b : Bool) (z : ℂ) :
    (affineMap b z : Threefold.Space) = FixedCoordinates.globalAxis (axisTriangle b) z := by
  cases b
  · exact (FixedCoordinates.globalAxis_eq_native ToricSpace.referenceTriangle z).symm
  · exact (FixedCoordinates.globalAxis_eq_native (Triangle.upperNeighbour 1) z).symm

theorem affineMap_isLocalDiffeomorph (b : Bool) :
    IsLocalDiffeomorph I₁ I₁ ω (affineMap b) := charts_affineMap_isLocalDiffeomorph 1 b

theorem affineMap_holomorphic (b : Bool) : ContMDiff I₁ I₁ ω (affineMap b) :=
  charts_affineMap_holomorphic 1 b

theorem affineMap_jointly_surjective (x : Curve 1) : ∃ b : Bool, ∃ z : ℂ, affineMap b z = x := by
  obtain h | h := (charts 1).covered x
  · obtain ⟨z, hz⟩ := h
    exact ⟨false, z, hz⟩
  · obtain ⟨z, hz⟩ := h
    exact ⟨true, z, hz⟩

/-- The actual native derivative of the literal curve inclusion. -/
def inclusionDerivative (x : Curve 1) : ℂ →L[ℂ] Model :=
  mfderiv I₁ IF (Subtype.val : Curve 1 → Threefold.Space) x

/-- The actual geometric tangent line of the named curve. -/
def tangentRange (x : Curve 1) : Submodule ℂ Model := (inclusionDerivative x).range

/-- The genuine native normal tangent quotient of the named global curve. -/
abbrev NormalFibre (x : Curve 1) := Model ⧸ tangentRange x

theorem tangentRange_isClosed (x : Curve 1) : IsClosed (tangentRange x : Set Model) :=
  (tangentRange x).closed_of_finiteDimensional

instance normalFibre_t2Space (x : Curve 1) : T2Space (NormalFibre x) := by
  let : IsClosed (tangentRange x : Set Model) := tangentRange_isClosed x
  infer_instance

/-- Chain rule in the original atlases, with the actual affine source map. -/
theorem affineMap_derivative_square (b : Bool) (z v : ℂ) :
    mfderiv I₁ IF (FixedCoordinates.globalAxis (axisTriangle b)) z v =
      inclusionDerivative (affineMap b z) (mfderiv I₁ I₁ (affineMap b) z v) := by
  have hfun : (Subtype.val : Curve 1 → Threefold.Space) ∘ affineMap b =
      FixedCoordinates.globalAxis (axisTriangle b) := funext (affineMap_val b)
  have hc := (affineMap_holomorphic b).mdifferentiableAt (by simp) (x := z)
  have hi := (inclusion_holomorphic 1).mdifferentiableAt (by simp)
    (x := affineMap b z)
  have h := (mfderiv_congr (I := I₁) (I' := IF) (x := z) hfun).symm.trans
    (mfderiv_comp z hi hc)
  exact congrArg (fun L : ℂ →L[ℂ] Model => L v) h

/-- The curve's native tangent range equals the actual cusp-axis tangent
range, since the affine source chart has an invertible derivative. -/
theorem tangentRange_affineMap (b : Bool) (z : ℂ) :
    tangentRange (affineMap b z) = FixedCoordinates.axisTangentRange (axisTriangle b) z := by
  have hs : Function.Surjective (mfderiv I₁ I₁ (affineMap b) z) :=
    ((affineMap_isLocalDiffeomorph b z).mfderivToContinuousLinearEquiv (by simp)).surjective
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    obtain ⟨t, ht⟩ := hs v
    refine ⟨t, ?_⟩
    exact (affineMap_derivative_square b z t).trans
      (congrArg (inclusionDerivative (affineMap b z)) ht)
  · rintro w ⟨v, rfl⟩
    exact ⟨mfderiv I₁ I₁ (affineMap b) z v, (affineMap_derivative_square b z v).symm⟩

/-- Identification of the two literal normal quotients by the proved
equality of their genuine tangent ranges. -/
def axisNormalTransport (b : Bool) (z : ℂ) :
    NormalFibre (affineMap b z) ≃L[ℂ]
      FixedCoordinates.AxisNormal (axisTriangle b) z :=
  { Submodule.quotEquivOfEq _ _ (tangentRange_affineMap b z) with
    continuous_toFun :=
      (tangentRange (affineMap b z)).isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.mpr
        continuous_quot_mk
    continuous_invFun := by
      let S := FixedCoordinates.axisTangentRange (axisTriangle b) z
      exact S.isOpenQuotientMap_mkQ.isQuotientMap.continuous_iff.mpr continuous_quot_mk }

@[simp] theorem axisNormalTransport_mk (b : Bool) (z : ℂ) (w : Model) :
    axisNormalTransport b z (Submodule.Quotient.mk w) = Submodule.Quotient.mk w := rfl

/-- Normal coordinates derived from the actual affine chart differential. -/
def normalEquiv (b : Bool) (z : ℂ) : NormalFibre (affineMap b z) ≃L[ℂ] CoordinateSpace 2 :=
  (axisNormalTransport b z).trans (FixedCoordinates.axisNormalEquiv (axisTriangle b) z)

@[simp] theorem normalEquiv_mk (b : Bool) (z : ℂ) (w : Model) :
    normalEquiv b z (Submodule.Quotient.mk w) =
      FixedCoordinates.normalProjection
        ((FixedCoordinates.tangentEquiv (axisTriangle b) (FixedCoordinates.axis z)).symm w) := rfl

theorem normalFibre_finrank (x : Curve 1) : Module.finrank ℂ (NormalFibre x) = 2 := by
  obtain ⟨b, z, rfl⟩ := affineMap_jointly_surjective x
  exact (normalEquiv b z).toLinearEquiv.finrank_eq.trans (by simp [CoordinateSpace])

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCurve
