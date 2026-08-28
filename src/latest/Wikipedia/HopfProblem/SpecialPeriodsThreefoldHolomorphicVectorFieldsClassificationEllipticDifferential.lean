import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticBaseChange

/-!
# The actual elliptic differential on vertical tangent vectors

The genuine elliptic gluing square consists of a logarithmic period
translation and a change of the source base coordinate.  Both exact
differentials fix the original vertical tangent vectors.
-/

noncomputable section

open Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification

open Elliptic HolomorphicForms.EllipticCover
open HolomorphicDifferentialForms.Coordinates

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] HolomorphicForms.EllipticCover.coverChartedSpace
  HolomorphicForms.EllipticCover.starCoverChartedSpace
  HolomorphicForms.EllipticCover.cover_isManifold
  HolomorphicForms.EllipticCover.starCover_isManifold
  HolomorphicForms.RegularCover.coverChartedSpace
  HolomorphicForms.RegularCover.cover_isManifold
  Threefold.chartedSpace Threefold.space_isManifold

/-- Changing the actual root base coordinate does not change a vertical
tangent vector in the original period marking. -/
theorem ellipticRegularCover_mfderiv_vertical (j : Kind) (x : CoverStar j)
    (u : ComplexPlane₂) :
    mfderiv IF IF (regularCover j) x (0, u) =
      mfderiv IF IF HolomorphicForms.RegularCover.globalCover
        (regularCoverToSource j x) (0, u) := by
  have hm : regularCover j =
      HolomorphicForms.RegularCover.globalCover ∘ regularCoverToSource j :=
    funext (regularCover_eq_sourceCover j)
  rw [hm, mfderiv_comp x
    (HolomorphicForms.RegularCover.globalCover_holomorphic.mdifferentiable (by simp) _)
    ((regularCoverToSource_holomorphic j).mdifferentiable (by simp) x)]
  change (mfderiv IF IF HolomorphicForms.RegularCover.globalCover
      (regularCoverToSource j x) : FamilyModel →L[ℂ] FamilyModel)
      ((mfderiv IF IF (regularCoverToSource j) x : FamilyModel →L[ℂ] FamilyModel)
        (0, u)) = _
  rw [mfderiv_regularCoverToSource]
  exact congrArg
    (mfderiv IF IF HolomorphicForms.RegularCover.globalCover
      (regularCoverToSource j x) : FamilyModel →L[ℂ] FamilyModel)
    (show EllipticBaseChange.baseChange (regularBaseJacobian j x.1) (0, u) = (0, u) by
      simp only [EllipticBaseChange.baseChange_apply, mul_zero])

/-- The same vertical vector is unchanged by the actual logarithmic
gauge shear and then the actual base-coordinate differential. -/
theorem ellipticGlobalCover_mfderiv_vertical (j : Kind) (x : CoverStar j)
    (u : ComplexPlane₂) :
    mfderiv IF IF (globalCover j) (starCoverInclusion j x) (0, u) =
      mfderiv IF IF HolomorphicForms.RegularCover.globalCover
        (regularCoverToSource j (gaugePoint j x)) (0, u) := by
  rw [globalCover_mfderiv_eq_regular_gauge]
  change (mfderiv IF IF (regularCover j) (gaugePoint j x) :
      FamilyModel →L[ℂ] FamilyModel) (EllipticShear.shear (gaugeDerivative j x.1) (0, u)) = _
  rw [EllipticShear.shear_vertical]
  exact ellipticRegularCover_mfderiv_vertical j (gaugePoint j x) u

/-- The point equality underlying the native differential comparison. -/
theorem ellipticGlobalCover_eq_regularSource (j : Kind) (x : CoverStar j) :
    globalCover j (starCoverInclusion j x) =
      HolomorphicForms.RegularCover.globalCover
        (regularCoverToSource j (gaugePoint j x)) :=
  (globalCover_eq_regularCover_localLog j x.1.property x).trans
    (regularCover_eq_sourceCover j (gaugePoint j x))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification
