import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationEllipticEtale
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationEllipticDifferential
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicVectorFieldsClassificationLift

/-!
# Genuine vector-field coefficients on the whole elliptic root cover

The actual root cover is locally biholomorphic also at root zero. Pulling
a native global field back through its invertible manifold differential
therefore gives a holomorphic native tangent section on this whole cover.
The literal fibre components on its zero section are holomorphic through
the elliptic center. On the puncture, the proved differential comparison
identifies vertical values with the regular period-vector coefficients.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification

open Elliptic HolomorphicForms.EllipticCover

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

attribute [local instance] HolomorphicForms.EllipticCover.coverChartedSpace
  HolomorphicForms.EllipticCover.starCoverChartedSpace
  HolomorphicForms.EllipticCover.cover_isManifold
  HolomorphicForms.EllipticCover.starCover_isManifold
  HolomorphicForms.RegularCover.coverChartedSpace
  HolomorphicForms.RegularCover.cover_isManifold
  Threefold.chartedSpace Threefold.space_isManifold

/-- The native lift through the actual full elliptic cover. -/
def ellipticLift (j : Kind) (v : Threefold.HolomorphicVectorFields.Field) :
    Wikipedia.HopfProblem.HolomorphicVectorFields.Field FamilyModel (Cover j) :=
  pullback (globalCover j) (ellipticGlobalCover_isLocalDiffeomorph j) v

/-- The unchanged native tangent components of the actual lift. -/
def ellipticCoefficients (j : Kind) (v : Threefold.HolomorphicVectorFields.Field)
    (x : Cover j) : FamilyModel := ellipticLift j v x

theorem ellipticCoefficients_holomorphic (j : Kind)
    (v : Threefold.HolomorphicVectorFields.Field) :
    ContMDiff IF IF ω (ellipticCoefficients j v) :=
  nativeValue_holomorphic_of_constant_charts FamilyModel (Cover j)
    (cover_chart_eq j) (ellipticLift j v)

/-- The native differential sends the literal coefficients back to the
original global field at the actual covering point. -/
theorem ellipticCoefficients_map (j : Kind) (v : Threefold.HolomorphicVectorFields.Field)
    (x : Cover j) :
    mfderiv IF IF (globalCover j) x (ellipticCoefficients j v x) =
      v (globalCover j x) :=
  pullback_map (globalCover j) (ellipticGlobalCover_isLocalDiffeomorph j) v x

/-- On the punctured cover, a genuine regular vertical value determines
exactly the same native tangent vector on the elliptic cover. -/
theorem ellipticCoefficients_eq_of_regular (j : Kind)
    (v : Threefold.HolomorphicVectorFields.Field) (x : CoverStar j) (u : ComplexPlane₂)
    (hu : regularCoefficients v (regularCoverToSource j (gaugePoint j x)) = (0, u)) :
    ellipticCoefficients j v (starCoverInclusion j x) = (0, u) := by
  apply (pullback_eq_iff (globalCover j)
    (ellipticGlobalCover_isLocalDiffeomorph j) v (starCoverInclusion j x) (0, u)).mpr
  rw [ellipticGlobalCover_mfderiv_vertical]
  have hm := regularLift_map v (regularCoverToSource j (gaugePoint j x))
  change mfderiv IF IF HolomorphicForms.RegularCover.globalCover
      (regularCoverToSource j (gaugePoint j x))
      (regularCoefficients v (regularCoverToSource j (gaugePoint j x))) = _ at hm
  rw [hu] at hm
  exact hm.trans (congrArg (fun y : Threefold.Space => (v y : FamilyModel))
    (ellipticGlobalCover_eq_regularSource j x).symm)

/-- Both fibre components of the actual lifted field on the zero section
of the full root cover, including root zero. -/
def ellipticVertical (j : Kind) (v : Threefold.HolomorphicVectorFields.Field)
    (z : Root j) : ComplexPlane₂ := (ellipticCoefficients j v (z, 0)).2

theorem ellipticVertical_holomorphic (j : Kind)
    (v : Threefold.HolomorphicVectorFields.Field) :
    ContMDiff I₁ I₂ ω (ellipticVertical j v) :=
  (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂).contMDiff.comp
    ((ellipticCoefficients_holomorphic j v).comp (zeroSection_holomorphic j))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicVectorFields.Classification
