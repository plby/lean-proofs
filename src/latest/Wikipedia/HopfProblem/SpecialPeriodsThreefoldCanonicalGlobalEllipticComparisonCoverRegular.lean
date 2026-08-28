import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonCoverGeometry
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonCoverPeriod
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalGeneratorElliptic

/-!
# The actual regular canonical form on the punctured elliptic cover

The period quotient, the actual inverse elliptic chart, and the original
logarithmic gluing are differentiated in their native atlases.  Pullback
of the actual regular section is consequently the genuine derivative of
the sphere coordinate, divided by the actual modular generator.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical
open HolomorphicForms.EllipticCover

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model

attribute [local instance] coverChartedSpace starCoverChartedSpace cover_isManifold
  starCover_isManifold Threefold.chartedSpace Threefold.space_isManifold
  HolomorphicForms.RegularCover.coverChartedSpace HolomorphicForms.RegularCover.cover_isManifold

local instance regularUpstairsChartedSpace : ChartedSpace Model SpecialRegularUpstairs :=
  specialRegularData.periods.totalChartedSpace

local instance regularUpstairsManifold : IsManifold I₃ ω SpecialRegularUpstairs :=
  specialRegularData.periods.totalSpace_isManifold

/-- The full intrinsic covector of the constructed section on its actual regular domain. -/
def regularCovector (y : regularLocus) : TopCovector :=
  Threefold.Canonical.intrinsicEquiv y.val (GlobalRegular.globalSection y)

/-- The original period-vector cover, with its proved regular-locus target. -/
def regularSourcePoint (x : HolomorphicForms.RegularCover.Cover) : regularLocus :=
  regularFamilyBiholomorph
    (GlobalRegular.familyQuotient (specialRegularData.periods.quotientMap x))

@[simp] theorem regularSourcePoint_val (x : HolomorphicForms.RegularCover.Cover) :
    (regularSourcePoint x : Threefold.Space) = HolomorphicForms.RegularCover.globalCover x :=
  rfl

/-- The untwisted root-coordinate cover is still a point of the original regular locus. -/
def untwistedPoint (j : Kind) (x : CoverStar j) : regularLocus :=
  regularSourcePoint (regularCoverToSource j x)

@[simp] theorem untwistedPoint_val (j : Kind) (x : CoverStar j) :
    (untwistedPoint j x : Threefold.Space) = regularCover j x := rfl

/-- The actual logarithmically reglued punctured cover lands in the regular locus. -/
def puncturedCoverPoint (j : Kind) (x : CoverStar j) : regularLocus :=
  ⟨globalCover j (starCoverInclusion j x),
    (globalCover_projection_mem_regular_iff j (starCoverInclusion j x)).mpr x.1.property⟩

@[simp] theorem puncturedCoverPoint_val (j : Kind) (x : CoverStar j) :
    (puncturedCoverPoint j x : Threefold.Space) =
      globalCover j (starCoverInclusion j x) := rfl

/-- This is equality of the actual regular-locus points, not an assumed gauge relation. -/
theorem puncturedCoverPoint_eq_untwisted (j : Kind) (x : CoverStar j) :
    puncturedCoverPoint j x = untwistedPoint j (gaugePoint j x) :=
  Subtype.ext (globalCover_eq_regularCover_localLog j x.1.property x)

/-- Pullback through the actual period-vector quotient leaves the native top volume unchanged. -/
theorem regularSource_covector_pullback (x : HolomorphicForms.RegularCover.Cover) :
    (regularCovector (regularSourcePoint x)).compContinuousLinearMap
      (mfderiv I₃ I₃ HolomorphicForms.RegularCover.globalCover x) =
        GlobalRegular.regularCoefficient x.1 • volume := by
  have hd : mfderiv I₃ I₃ HolomorphicForms.RegularCover.globalCover x =
      (mfderiv I₃ I₃ GlobalRegular.upstairsGlobalMap
        (specialRegularData.periods.quotientMap x)).comp
          (mfderiv I₃ I₃ specialRegularData.periods.quotientMap x) :=
    mfderiv_comp x
      (GlobalRegular.upstairsGlobalMap_isLocalDiffeomorph.contMDiff.mdifferentiable
        (by simp) _)
      (specialRegularData.periods.quotientMap_holomorphic.mdifferentiable (by simp) x)
  have hp := GlobalRegular.globalSection_intrinsic_pullback
    (specialRegularData.periods.quotientMap x)
  change (regularCovector (regularSourcePoint x)).compContinuousLinearMap
      (mfderiv I₃ I₃ GlobalRegular.upstairsGlobalMap
        (specialRegularData.periods.quotientMap x)) =
    GlobalRegular.regularCoefficient x.1 • volume at hp
  have hchain := congrArg (fun L : Model →L[ℂ] Model =>
    (regularCovector (regularSourcePoint x)).compContinuousLinearMap L) hd
  change _ = ((regularCovector (regularSourcePoint x)).compContinuousLinearMap
      (mfderiv I₃ I₃ GlobalRegular.upstairsGlobalMap
        (specialRegularData.periods.quotientMap x))).compContinuousLinearMap
          (mfderiv I₃ I₃ specialRegularData.periods.quotientMap x) at hchain
  exact hchain.trans ((congrArg (fun α : TopCovector => α.compContinuousLinearMap
    (mfderiv I₃ I₃ specialRegularData.periods.quotientMap x)) hp).trans
      (periodQuotient_topCovector_pullback (fun z : TriangleRegularPoint => (z.val : ℂ))
        regularPoint_chart_apply specialRegularData.periods
        (GlobalRegular.regularCoefficient x.1 • volume) x))

/-- The actual numerator is the original sphere-coordinate derivative in root coordinates. -/
def coverRegularCoefficient (j : Kind) (s : RootStar j) : ℂ :=
  GlobalRegular.coordinateDerivative (regularBase j s) * baseJacobian j s.val /
    GlobalGenerator.discGenerator j s.val.val

theorem coverRegularCoefficient_eq (j : Kind) (s : RootStar j) :
    coverRegularCoefficient j s =
      GlobalRegular.regularCoefficient (regularBase j s) * baseJacobian j s.val := by
  change (_ * _ / GlobalGenerator.generator (neighborhoodLift j s.val.val)) =
    (_ / GlobalGenerator.generator (neighborhoodLift j s.val.val)) * _
  ring

/-- Pullback to the actual untwisted elliptic cover, before logarithmic regluing. -/
theorem untwisted_covector_pullback (j : Kind) (x : CoverStar j) :
    (regularCovector (untwistedPoint j x)).compContinuousLinearMap
      (mfderiv I₃ I₃ (regularCover j) x) = coverRegularCoefficient j x.1 • volume := by
  have hd : mfderiv I₃ I₃ (regularCover j) x =
      (mfderiv I₃ I₃ HolomorphicForms.RegularCover.globalCover
        (regularCoverToSource j x)).comp
          (mfderiv I₃ I₃ (regularCoverToSource j) x) :=
    mfderiv_comp x
      (HolomorphicForms.RegularCover.globalCover_holomorphic.mdifferentiable (by simp) _)
      ((regularCoverToSource_holomorphic j).mdifferentiable (by simp) x)
  have hchain := congrArg (fun L : Model →L[ℂ] Model =>
    (regularCovector (untwistedPoint j x)).compContinuousLinearMap L) hd
  change _ = ((regularCovector (untwistedPoint j x)).compContinuousLinearMap
      (mfderiv I₃ I₃ HolomorphicForms.RegularCover.globalCover
        (regularCoverToSource j x))).compContinuousLinearMap
          (mfderiv I₃ I₃ (regularCoverToSource j) x) at hchain
  have hp := regularSource_covector_pullback (regularCoverToSource j x)
  have hbase := congrArg (fun L : Model →L[ℂ] Model =>
    (GlobalRegular.regularCoefficient (regularBase j x.1) • volume).compContinuousLinearMap L)
      (mfderiv_regularCoverToSource j x)
  have hscale :
      (HolomorphicForms.EllipticCover.regularBaseJacobian j x.1) •
        (GlobalRegular.regularCoefficient (regularBase j x.1) • volume) =
          coverRegularCoefficient j x.1 • volume := by
    have hj : regularBaseJacobian j x.1 = baseJacobian j x.1.val :=
      mfderiv_regularBase_one j x.1
    rw [smul_smul, coverRegularCoefficient_eq, hj, mul_comm]
  exact hchain.trans ((congrArg (fun α : TopCovector => α.compContinuousLinearMap
    (mfderiv I₃ I₃ (regularCoverToSource j) x)) hp).trans
      (hbase.trans ((topCovector_baseChange _ _).trans hscale)))

/-- The genuine logarithmic gauge preserves the complete pulled-back top covector. -/
theorem globalRegular_cover_pullback (j : Kind) (x : CoverStar j) :
    (regularCovector (puncturedCoverPoint j x)).compContinuousLinearMap
      (mfderiv I₃ I₃ (globalCover j) (starCoverInclusion j x)) =
        coverRegularCoefficient j x.1 • volume := by
  rw [puncturedCoverPoint_eq_untwisted]
  have hd := globalCover_mfderiv_eq_regular_gauge j x
  have hchain := congrArg (fun L : Model →L[ℂ] Model =>
    (regularCovector (untwistedPoint j (gaugePoint j x))).compContinuousLinearMap L) hd
  change _ = ((regularCovector (untwistedPoint j (gaugePoint j x))).compContinuousLinearMap
      (mfderiv I₃ I₃ (regularCover j) (gaugePoint j x))).compContinuousLinearMap
        (HolomorphicDifferentialForms.Coordinates.EllipticShear.shear
          (gaugeDerivative j x.1)) at hchain
  have hp := untwisted_covector_pullback j (gaugePoint j x)
  exact hchain.trans ((congrArg (fun α : TopCovector => α.compContinuousLinearMap
    (HolomorphicDifferentialForms.Coordinates.EllipticShear.shear
      (gaugeDerivative j x.1))) hp).trans
        (HolomorphicDifferentialForms.Coordinates.EllipticShear.top_pullback _ _))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticComparison
