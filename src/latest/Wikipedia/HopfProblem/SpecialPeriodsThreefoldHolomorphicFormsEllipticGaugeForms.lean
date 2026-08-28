import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticCoverForms
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticRestriction
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticShearManifold
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticShearCoefficients

/-!
# The exact gauge comparison of genuine elliptic pullback forms

The actual equality of the two covering maps is differentiated in their
unchanged native atlases. The resulting pullback identity is an equality
of full continuous alternating covectors. Evaluating it proves the
coefficient identities used in the elliptic extension argument, including
the correction terms which must vanish before the base one-form and mixed
two-form coefficients can be declared unchanged.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover

open Elliptic EllipticFilling CuspUniformization HolomorphicDifferentialForms
  HolomorphicDifferentialForms.Coordinates HolomorphicDifferentialForms.Coordinates.EllipticShear

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

attribute [local instance] coverChartedSpace starCoverChartedSpace Threefold.chartedSpace
  cover_isManifold starCover_isManifold Threefold.space_isManifold

/-- The actual logarithmic period section in a chosen local branch. -/
def gaugeSection (j : Kind) (z₀ : ℂ) (z : RootStar j) : ComplexPlane₂ :=
  localLog z₀ (rootCoordinate j z.val) •
    LogGauge.periodVector (specialLocalData j).periods j.twist z.val.val

theorem gaugeSection_holomorphicAt (j : Kind) (z : RootStar j) :
    ContMDiffAt I₁ I₂ ω (gaugeSection j (rootCoordinate j z.val)) z := by
  have hc : ContMDiff I₁ I₁ ω (fun w : RootStar j => rootCoordinate j w.val) :=
    (rootCoordinate_holomorphic j).comp contMDiff_subtype_val
  have hp : ContMDiff I₁ I₂ ω (fun w : RootStar j =>
      LogGauge.periodVector (specialLocalData j).periods j.twist w.val.val) :=
    (LogGauge.periodVector_holomorphic (specialLocalData j).periods j.twist).comp
      (contMDiff_subtype_val.comp contMDiff_subtype_val)
  exact ((localLog_contDiffAt z.property).contMDiffAt.comp z (hc z)).smul (hp z)

/-- The local gauge is holomorphic at its selected nonzero root. -/
theorem gaugeLift_localLog_holomorphicAt (j : Kind) (x : CoverStar j) :
    ContMDiffAt IF IF ω (gaugeLift j (localLog (rootCoordinate j x.1.val))) x :=
  contMDiffAt_gaugeTranslationOn (gaugeSection_holomorphicAt j x.1) x.2

/-- The actual base derivative of the genuine local logarithmic section. -/
def gaugeDerivative (j : Kind) (z : RootStar j) : ComplexPlane₂ :=
  mfderiv I₁ I₂ (gaugeSection j (rootCoordinate j z.val)) z (1 : ℂ)

/-- The exact three-dimensional manifold derivative is the genuine shear. -/
theorem mfderiv_gaugeLift_localLog (j : Kind) (x : CoverStar j) :
    mfderiv IF IF (gaugeLift j (localLog (rootCoordinate j x.1.val))) x =
      shear (gaugeDerivative j x.1) :=
  mfderiv_gaugeTranslationOn
    ((gaugeSection_holomorphicAt j x.1).mdifferentiableAt (by simp)) x.2

/-- The actual regular-family form pulled back to the punctured root cover. -/
def regularCoverPullback (j : Kind) {p : ℕ} :
    Form FamilyModel Threefold.Space p →ₗ[ℂ] Form FamilyModel (CoverStar j) p :=
  pullback (regularCover j) (regularCover_holomorphic j)

@[simp] theorem regularCoverPullback_apply (j : Kind) {p : ℕ}
    (θ : Form FamilyModel Threefold.Space p) (x : CoverStar j) :
    regularCoverPullback j θ x =
      (θ (regularCover j x)).compContinuousLinearMap (mfderiv IF IF (regularCover j) x) := rfl

/-- Choose the branch centered at the actual source root, retaining the
same point in the globally defined logarithmic torus translation. -/
def gaugePoint (j : Kind) (x : CoverStar j) : CoverStar j :=
  gaugeLift j (localLog (rootCoordinate j x.1.val)) x

@[simp] theorem gaugePoint_fst (j : Kind) (x : CoverStar j) : (gaugePoint j x).1 = x.1 := rfl

/-- The differentiated actual gluing square, before applying any covector. -/
theorem globalCover_mfderiv_eq_regular_gauge (j : Kind) (x : CoverStar j) :
    mfderiv IF IF (globalCover j) (starCoverInclusion j x) =
      (mfderiv IF IF (regularCover j) (gaugePoint j x)).comp
        (shear (gaugeDerivative j x.1)) := by
  let g := gaugeLift j (localLog (rootCoordinate j x.1.val))
  let L : FamilyModel →L[ℂ] FamilyModel :=
    mfderiv IF IF (globalCover j) (starCoverInclusion j x)
  let R : FamilyModel →L[ℂ] FamilyModel := mfderiv IF IF (regularCover j) (g x)
  have hg : HasMFDerivAt IF IF g x (shear (gaugeDerivative j x.1)) :=
    ((gaugeLift_localLog_holomorphicAt j x).mdifferentiableAt (by simp)).hasMFDerivAt
      |>.congr_mfderiv (mfderiv_gaugeLift_localLog j x)
  have hi : HasMFDerivAt IF IF (starCoverInclusion j) x
      (ContinuousLinearMap.id ℂ FamilyModel) :=
    ((starCoverInclusion_holomorphic j x).mdifferentiableAt (by simp)).hasMFDerivAt
      |>.congr_mfderiv (mfderiv_starCoverInclusion j x)
  have hL : HasMFDerivAt IF IF (globalCover j) (starCoverInclusion j x) L :=
    ((globalCover_holomorphic j (starCoverInclusion j x)).mdifferentiableAt
      (by simp)).hasMFDerivAt
  have hR : HasMFDerivAt IF IF (regularCover j) (g x) R :=
    ((regularCover_holomorphic j (g x)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hmaps : globalCover j ∘ starCoverInclusion j = regularCover j ∘ g :=
    funext (globalCover_eq_regularCover_localLog j x.1.property)
  have hleft : HasMFDerivAt IF IF (globalCover j ∘ starCoverInclusion j) x L :=
    (hL.comp x hi).congr_mfderiv (by ext v; rfl)
  have hright : HasMFDerivAt IF IF (globalCover j ∘ starCoverInclusion j) x
      (R.comp (shear (gaugeDerivative j x.1))) :=
    (hR.comp x hg).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (congrFun hmaps))
  have he := hasMFDerivAt_unique hleft hright
  exact he

/-- Exact equality of the full genuine alternating covectors under the
actual logarithmic regluing, in every degree. -/
theorem globalCoverPullback_eq_regularCoverPullback_shear (j : Kind) {p : ℕ}
    (θ : Form FamilyModel Threefold.Space p) (x : CoverStar j) :
    globalCoverPullback j θ (starCoverInclusion j x) =
      (regularCoverPullback j θ (gaugePoint j x)).compContinuousLinearMap
        (shear (gaugeDerivative j x.1)) := by
  rw [globalCoverPullback_apply, regularCoverPullback_apply,
    globalCover_mfderiv_eq_regular_gauge,
    globalCover_eq_regularCover_localLog j x.1.property x]
  rfl

/-- The vertical one-form coefficient is unchanged under the exact gauge. -/
theorem oneFibreCoefficient_gauge (j : Kind)
    (θ : Form FamilyModel Threefold.Space 1) (x : CoverStar j) :
    oneFibreCoefficient (globalCoverPullback j θ (starCoverInclusion j x)) =
      oneFibreCoefficient (regularCoverPullback j θ (gaugePoint j x)) := by
  rw [globalCoverPullback_eq_regularCoverPullback_shear]
  exact oneFibreCoefficient_pullback (regularCoverPullback j θ (gaugePoint j x)) _

/-- The one-form base coefficient retains its actual logarithmic correction. -/
theorem oneBaseCoefficient_gauge (j : Kind)
    (θ : Form FamilyModel Threefold.Space 1) (x : CoverStar j) :
    oneBaseCoefficient (globalCoverPullback j θ (starCoverInclusion j x)) =
      oneBaseCoefficient (regularCoverPullback j θ (gaugePoint j x)) +
        dotProduct (oneFibreCoefficient (regularCoverPullback j θ (gaugePoint j x)))
          (gaugeDerivative j x.1) := by
  rw [globalCoverPullback_eq_regularCoverPullback_shear]
  exact oneBaseCoefficient_pullback (regularCoverPullback j θ (gaugePoint j x)) _

/-- When the fibre coefficient vanishes, the one-form base
coefficient is unchanged. No unconditional extension of that coefficient
is asserted before this vanishing argument. -/
theorem oneBaseCoefficient_gauge_of_fibre_zero (j : Kind)
    (θ : Form FamilyModel Threefold.Space 1) (x : CoverStar j)
    (hc : oneFibreCoefficient (regularCoverPullback j θ (gaugePoint j x)) = 0) :
    oneBaseCoefficient (globalCoverPullback j θ (starCoverInclusion j x)) =
      oneBaseCoefficient (regularCoverPullback j θ (gaugePoint j x)) := by
  rw [oneBaseCoefficient_gauge, hc, zero_dotProduct, add_zero]

theorem twoVerticalCoefficient_gauge (j : Kind)
    (θ : Form FamilyModel Threefold.Space 2) (x : CoverStar j) :
    twoVerticalCoefficient (globalCoverPullback j θ (starCoverInclusion j x)) =
      twoVerticalCoefficient (regularCoverPullback j θ (gaugePoint j x)) := by
  rw [globalCoverPullback_eq_regularCoverPullback_shear]
  exact twoVerticalCoefficient_pullback (regularCoverPullback j θ (gaugePoint j x)) _

/-- The mixed two-form coefficient retains the exact vertical-area correction. -/
theorem twoMixedCoefficient_gauge (j : Kind)
    (θ : Form FamilyModel Threefold.Space 2) (x : CoverStar j) :
    twoMixedCoefficient (globalCoverPullback j θ (starCoverInclusion j x)) =
      twoMixedCoefficient (regularCoverPullback j θ (gaugePoint j x)) +
        twoVerticalCoefficient (regularCoverPullback j θ (gaugePoint j x)) •
          PeriodFamilyHolomorphicForms.skewPeriod (gaugeDerivative j x.1) := by
  rw [globalCoverPullback_eq_regularCoverPullback_shear]
  exact twoMixedCoefficient_pullback (regularCoverPullback j θ (gaugePoint j x)) _

theorem twoMixedCoefficient_gauge_of_vertical_zero (j : Kind)
    (θ : Form FamilyModel Threefold.Space 2) (x : CoverStar j)
    (ha : twoVerticalCoefficient (regularCoverPullback j θ (gaugePoint j x)) = 0) :
    twoMixedCoefficient (globalCoverPullback j θ (starCoverInclusion j x)) =
      twoMixedCoefficient (regularCoverPullback j θ (gaugePoint j x)) := by
  rw [twoMixedCoefficient_gauge, ha, zero_smul, add_zero]

/-- The genuine top-form coefficient is unchanged with no lower-degree premise. -/
theorem topCoefficient_gauge (j : Kind)
    (θ : Form FamilyModel Threefold.Space 3) (x : CoverStar j) :
    topCoefficient (globalCoverPullback j θ (starCoverInclusion j x)) =
      topCoefficient (regularCoverPullback j θ (gaugePoint j x)) := by
  rw [globalCoverPullback_eq_regularCoverPullback_shear]
  exact topCoefficient_pullback (regularCoverPullback j θ (gaugePoint j x)) _

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover
