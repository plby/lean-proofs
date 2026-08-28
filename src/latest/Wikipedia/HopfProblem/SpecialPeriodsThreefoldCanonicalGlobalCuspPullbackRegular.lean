import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspPullbackRegularCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalRegular
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspComparison

/-!
# Pullback of the actual global regular canonical section to the cusp cover

The maps in these statements are the original period-vector quotient,
triangle quotient, and inclusions into the glued threefold.  The exact
global comparison of logarithmic cusp and regular covers lets their actual
derivatives recover the regular canonical form with its base-width factor.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspPullback

open TrianglePeriodFamily.Canonical
open HolomorphicForms.Cusp GlobalRegular

local notation "I₃" => modelWithCornersSelf ℂ Model

attribute [local instance] HolomorphicForms.RegularCover.coverChartedSpace
  HolomorphicForms.RegularCover.cover_isManifold Threefold.chartedSpace

local instance regularUpstairsChartedSpace : ChartedSpace Model SpecialRegularUpstairs :=
  specialRegularData.periods.totalChartedSpace

local instance regularUpstairsManifold : IsManifold I₃ ω SpecialRegularUpstairs :=
  specialRegularData.periods.totalSpace_isManifold

local instance regularGlobalManifold : IsManifold I₃ ω Threefold.Space :=
  Threefold.space_isManifold

/-- The original period-vector quotient after the unchanged logarithmic comparison. -/
def logToRegularFamily (x : LogDomain) : SpecialRegularUpstairs :=
  specialRegularData.periods.quotientMap (toRegularCover x)

theorem logToRegularFamily_holomorphic : ContMDiff I₃ I₃ ω logToRegularFamily :=
  specialRegularData.periods.quotientMap_holomorphic.comp toRegularCover_holomorphic

/-- Pullback of the actual upstairs family form through the actual cusp comparison. -/
theorem regularFamilyVolume_log_pullback (x : LogDomain) :
    (specialUpstairsForm (logToRegularFamily x)).compContinuousLinearMap
      (mfderiv I₃ I₃ logToRegularFamily x) = (Triangle.width : ℂ) • volume := by
  have hq := specialRegularData.periods.quotientMap_holomorphic.mdifferentiable (by simp)
  change ContinuousAlternatingMap.compContinuousLinearMap
    (specialUpstairsForm (specialRegularData.periods.quotientMap (toRegularCover x)))
      (mfderiv I₃ I₃ (specialRegularData.periods.quotientMap ∘ toRegularCover) x) = _
  rw [mfderiv_comp x (hq (toRegularCover x))
    (toRegularCover_holomorphic.mdifferentiable (by simp) x)]
  change ContinuousAlternatingMap.compContinuousLinearMap ((specialUpstairsForm
    (specialRegularData.periods.quotientMap (toRegularCover x))).compContinuousLinearMap
      (mfderiv I₃ I₃ specialRegularData.periods.quotientMap (toRegularCover x)))
        (mfderiv I₃ I₃ toRegularCover x) = _
  rw [show (specialUpstairsForm
      (specialRegularData.periods.quotientMap (toRegularCover x))).compContinuousLinearMap
        (mfderiv I₃ I₃ specialRegularData.periods.quotientMap (toRegularCover x)) = volume from
    familyVolume_periodQuotient_pullback (fun z : TriangleRegularPoint => (z.val : ℂ))
      regularPoint_chart_apply specialRegularData.periods (toRegularCover x)]
  exact toRegularCover_volume_pullback x

/-- The actual regular-cover point, with its proved membership in the full global regular locus. -/
def regularCoverPoint (x : HolomorphicForms.RegularCover.Cover) : regularLocus :=
  regularFamilyBiholomorph (familyQuotient (specialRegularData.periods.quotientMap x))

@[simp] theorem regularCoverPoint_val (x : HolomorphicForms.RegularCover.Cover) :
    (regularCoverPoint x : Threefold.Space) = HolomorphicForms.RegularCover.globalCover x := rfl

/-- The entire period-vector cover maps by the original family quotient and inclusion. -/
theorem regularCover_eq_upstairs_comp :
    HolomorphicForms.RegularCover.globalCover =
      upstairsGlobalMap ∘ specialRegularData.periods.quotientMap := rfl

/-- The actual global regular canonical section pulls back to its original
coefficient times volume. -/
theorem globalSection_regularCover_pullback (x : HolomorphicForms.RegularCover.Cover) :
    (intrinsicEquiv (HolomorphicForms.RegularCover.globalCover x)
      (globalSection (regularCoverPoint x))).compContinuousLinearMap
        (mfderiv I₃ I₃ HolomorphicForms.RegularCover.globalCover x) =
          regularCoefficient x.1 • volume := by
  rw [regularCover_eq_upstairs_comp, mfderiv_comp x
    (upstairsGlobalMap_isLocalDiffeomorph.contMDiff.mdifferentiable (by simp)
      (specialRegularData.periods.quotientMap x))
    (specialRegularData.periods.quotientMap_holomorphic.mdifferentiable (by simp) x)]
  change ContinuousAlternatingMap.compContinuousLinearMap
    ((intrinsicEquiv (upstairsGlobalMap (specialRegularData.periods.quotientMap x))
    (globalSection (regularFamilyBiholomorph
      (familyQuotient (specialRegularData.periods.quotientMap x))))).compContinuousLinearMap
        (mfderiv I₃ I₃ upstairsGlobalMap (specialRegularData.periods.quotientMap x)))
          (mfderiv I₃ I₃ specialRegularData.periods.quotientMap x) = _
  rw [globalSection_intrinsic_pullback]
  change regularCoefficient x.1 •
    (volume.compContinuousLinearMap (mfderiv I₃ I₃ specialRegularData.periods.quotientMap x)) = _
  rw [periodQuotient_volume_pullback (fun z : TriangleRegularPoint => (z.val : ℂ))
    regularPoint_chart_apply specialRegularData.periods x]
  rfl

/-- The logarithmic cusp covering point lies in the actual regular open set. -/
def regularLogPoint (x : LogDomain) : regularLocus :=
  ⟨globalLogMap x, by
    rw [globalLogMap_eq_regularCover]
    exact (regularCoverPoint (toRegularCover x)).property⟩

@[simp] theorem regularLogPoint_val (x : LogDomain) :
    (regularLogPoint x : Threefold.Space) = globalLogMap x := rfl

theorem regularLogPoint_eq (x : LogDomain) :
    regularLogPoint x = regularCoverPoint (toRegularCover x) :=
  Subtype.ext (globalLogMap_eq_regularCover x)

/-- The genuine global section has the exact width-scaled native coefficient
on the cusp log cover. -/
theorem globalSection_log_pullback (x : LogDomain) :
    (intrinsicEquiv (globalLogMap x) (globalSection (regularLogPoint x))).compContinuousLinearMap
      (mfderiv I₃ I₃ globalLogMap x) =
        ((Triangle.width : ℂ) * regularCoefficient (toRegularCover x).1) • volume := by
  have hpoint := regularLogPoint_eq x
  have hform : intrinsicEquiv (globalLogMap x) (globalSection (regularLogPoint x)) =
      intrinsicEquiv (HolomorphicForms.RegularCover.globalCover (toRegularCover x))
        (globalSection (regularCoverPoint (toRegularCover x))) := by
    exact congrArg (β := TopCovector)
      (fun y : regularLocus => intrinsicEquiv y.val (globalSection y)) hpoint
  rw [hform, globalLogMap_eq_regularCover_comp, mfderiv_comp x
    (HolomorphicForms.RegularCover.globalCover_holomorphic.mdifferentiable (by simp)
      (toRegularCover x))
    (toRegularCover_holomorphic.mdifferentiable (by simp) x)]
  change ContinuousAlternatingMap.compContinuousLinearMap
    ((intrinsicEquiv (HolomorphicForms.RegularCover.globalCover (toRegularCover x))
    (globalSection (regularCoverPoint (toRegularCover x)))).compContinuousLinearMap
      (mfderiv I₃ I₃ HolomorphicForms.RegularCover.globalCover (toRegularCover x)))
        (mfderiv I₃ I₃ toRegularCover x) = _
  rw [globalSection_regularCover_pullback]
  change regularCoefficient (toRegularCover x).1 •
    (volume.compContinuousLinearMap (mfderiv I₃ I₃ toRegularCover x)) = _
  rw [toRegularCover_volume_pullback]
  change (regularCoefficient (toRegularCover x).1 • ((Triangle.width : ℂ) • volume) :
    TopCovector) = ((Triangle.width : ℂ) * regularCoefficient (toRegularCover x).1) • volume
  rw [smul_smul, mul_comm]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspPullback
