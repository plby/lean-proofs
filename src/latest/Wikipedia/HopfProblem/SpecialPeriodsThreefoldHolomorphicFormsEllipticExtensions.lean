import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticBaseChange
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticCoverCoefficients
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticJacobian
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsNormalForms
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Holomorphic coefficient extensions at the actual elliptic roots

Every function below is extracted from the genuine pullback of an
arbitrary global holomorphic form. The actual logarithmic gauge and the
proved global period normal forms identify its punctured values with the
original upper-half-plane coefficients. The inverse chart Jacobian is
holomorphic and nonzero also at the center, so its division creates no
extension assumption. The one-form base coefficient agrees only after
the vertical coefficient has been proved zero, as required by Lemma 9.16(i).
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover

open Elliptic HolomorphicDifferentialForms HolomorphicDifferentialForms.Coordinates

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FamilyModel

attribute [local instance] coverChartedSpace starCoverChartedSpace Threefold.chartedSpace
  cover_isManifold starCover_isManifold Threefold.space_isManifold
  RegularCover.coverChartedSpace RegularCover.cover_isManifold

theorem regularBaseJacobian_eq (j : Kind) (z : RootStar j) :
    regularBaseJacobian j z = baseJacobian j z.val := mfderiv_regularBase_one j z

/-- The actual period normal form removes the complex fibre variable. -/
theorem regularCover_oneFibre (j : Kind) (θ : Form FamilyModel Threefold.Space 1)
    (x : CoverStar j) :
    oneFibreCoefficient (regularCoverPullback j θ x) =
      RegularCover.fibreOne θ (regularBase j x.1) :=
  (oneFibreCoefficient_source j θ x).trans
    (RegularCover.oneFibre_eq_fibreOne θ (regularBase j x.1) x.2)

theorem regularCover_oneBase (j : Kind) (θ : Form FamilyModel Threefold.Space 1)
    (x : CoverStar j) :
    oneBaseCoefficient (regularCoverPullback j θ x) =
      baseJacobian j x.1.val * RegularCover.baseOne θ (regularBase j x.1) := by
  rw [oneBaseCoefficient_source, regularBaseJacobian_eq]
  exact congrArg (fun a => baseJacobian j x.1.val * a)
    (RegularCover.oneBase_eq_baseOne θ (regularBase j x.1) x.2)

/-- The vertical two-form coefficient vanishes for every genuine global
form, using the actual special-period calculation rather than a premise. -/
theorem regularCover_twoVertical_eq_zero (j : Kind)
    (θ : Form FamilyModel Threefold.Space 2) (x : CoverStar j) :
    twoVerticalCoefficient (regularCoverPullback j θ x) = 0 :=
  (twoVerticalCoefficient_source j θ x).trans
    (RegularCover.twoVertical_eq_zero θ (regularBase j x.1) x.2)

theorem regularCover_twoMixed (j : Kind) (θ : Form FamilyModel Threefold.Space 2)
    (x : CoverStar j) :
    twoMixedCoefficient (regularCoverPullback j θ x) =
      baseJacobian j x.1.val • RegularCover.mixedTwo θ (regularBase j x.1) := by
  rw [twoMixedCoefficient_source, regularBaseJacobian_eq]
  exact congrArg (fun b => baseJacobian j x.1.val • b)
    (RegularCover.twoMixed_eq_mixedTwo θ (regularBase j x.1) x.2)

theorem regularCover_top (j : Kind) (θ : Form FamilyModel Threefold.Space 3)
    (x : CoverStar j) :
    topCoefficient (regularCoverPullback j θ x) =
      baseJacobian j x.1.val * RegularCover.baseTop θ (regularBase j x.1) := by
  rw [topCoefficient_source, regularBaseJacobian_eq]
  exact congrArg (fun c => baseJacobian j x.1.val * c)
    (RegularCover.top_eq_baseTop θ (regularBase j x.1) x.2)

/-- The vertical one-form coefficient on the whole genuine root domain. -/
def oneFibreExtension (j : Kind) (θ : Form FamilyModel Threefold.Space 1) :
    Root j → ComplexPlane₂ := oneFibreCoefficient ∘ globalCoverZeroCoefficients j θ

theorem oneFibreExtension_holomorphic (j : Kind)
    (θ : Form FamilyModel Threefold.Space 1) : ContMDiff I₁ I₂ ω (oneFibreExtension j θ) :=
  oneFibreCoefficient.contMDiff.comp (globalCoverZeroCoefficients_holomorphic j θ)

/-- The exact gauge and actual period normal form prove agreement at
every punctured root, not merely along a selected approach to the center. -/
theorem oneFibreExtension_eq (j : Kind) (θ : Form FamilyModel Threefold.Space 1)
    (z : RootStar j) :
    oneFibreExtension j θ z.val = RegularCover.fibreOne θ (regularBase j z) := by
  change oneFibreCoefficient (globalCoverZeroCoefficients j θ z.val) = _
  rw [globalCoverZeroCoefficients_apply, globalCoverNativeCoefficients_eq]
  change oneFibreCoefficient (globalCoverPullback j θ (starCoverInclusion j (z, 0))) = _
  exact (oneFibreCoefficient_gauge j θ (z, 0)).trans
    (regularCover_oneFibre j θ (gaugePoint j (z, 0)))

/-- The mixed two-form coefficient, restored to the original base coordinate. -/
def twoMixedExtension (j : Kind) (θ : Form FamilyModel Threefold.Space 2)
    (z : Root j) : ComplexPlane₂ :=
  (baseJacobian j z)⁻¹ • twoMixedCoefficient (globalCoverZeroCoefficients j θ z)

theorem twoMixedExtension_holomorphic (j : Kind)
    (θ : Form FamilyModel Threefold.Space 2) : ContMDiff I₁ I₂ ω (twoMixedExtension j θ) :=
  ((baseJacobian_holomorphic j).inv₀ (baseJacobian_ne_zero j)).smul
    (twoMixedCoefficient.contMDiff.comp (globalCoverZeroCoefficients_holomorphic j θ))

/-- The vertical correction is discharged by the proved normal form;
the actual nonzero Jacobian then cancels. -/
theorem twoMixedExtension_eq (j : Kind) (θ : Form FamilyModel Threefold.Space 2)
    (z : RootStar j) :
    twoMixedExtension j θ z.val = RegularCover.mixedTwo θ (regularBase j z) := by
  have he : twoMixedCoefficient (globalCoverZeroCoefficients j θ z.val) =
      baseJacobian j z.val • RegularCover.mixedTwo θ (regularBase j z) := by
    rw [globalCoverZeroCoefficients_apply, globalCoverNativeCoefficients_eq]
    change twoMixedCoefficient (globalCoverPullback j θ (starCoverInclusion j (z, 0))) = _
    exact (twoMixedCoefficient_gauge_of_vertical_zero j θ (z, 0)
      (regularCover_twoVertical_eq_zero j θ (gaugePoint j (z, 0)))).trans
      (regularCover_twoMixed j θ (gaugePoint j (z, 0)))
  change (baseJacobian j z.val)⁻¹ •
    twoMixedCoefficient (globalCoverZeroCoefficients j θ z.val) = _
  rw [he, smul_smul, inv_mul_cancel₀ (baseJacobian_ne_zero j z.val), one_smul]

/-- The top-form coefficient in the original base coordinate on the entire root domain. -/
def topExtension (j : Kind) (θ : Form FamilyModel Threefold.Space 3) (z : Root j) : ℂ :=
  (baseJacobian j z)⁻¹ * topCoefficient (globalCoverZeroCoefficients j θ z)

theorem topExtension_holomorphic (j : Kind) (θ : Form FamilyModel Threefold.Space 3) :
    ContMDiff I₁ I₁ ω (topExtension j θ) :=
  ((baseJacobian_holomorphic j).inv₀ (baseJacobian_ne_zero j)).mul
    (topCoefficient.contMDiff.comp (globalCoverZeroCoefficients_holomorphic j θ))

theorem topExtension_eq (j : Kind) (θ : Form FamilyModel Threefold.Space 3)
    (z : RootStar j) :
    topExtension j θ z.val = RegularCover.baseTop θ (regularBase j z) := by
  have he : topCoefficient (globalCoverZeroCoefficients j θ z.val) =
      baseJacobian j z.val * RegularCover.baseTop θ (regularBase j z) := by
    rw [globalCoverZeroCoefficients_apply, globalCoverNativeCoefficients_eq]
    change topCoefficient (globalCoverPullback j θ (starCoverInclusion j (z, 0))) = _
    exact (topCoefficient_gauge j θ (z, 0)).trans
      (regularCover_top j θ (gaugePoint j (z, 0)))
  change (baseJacobian j z.val)⁻¹ * topCoefficient (globalCoverZeroCoefficients j θ z.val) = _
  rw [he, ← mul_assoc, inv_mul_cancel₀ (baseJacobian_ne_zero j z.val), one_mul]

/-- A holomorphic candidate for the one-form base coefficient; agreement
with the regular coefficient is only asserted under its vanishing fibre premise. -/
def oneBaseExtension (j : Kind) (θ : Form FamilyModel Threefold.Space 1) (z : Root j) : ℂ :=
  (baseJacobian j z)⁻¹ * oneBaseCoefficient (globalCoverZeroCoefficients j θ z)

theorem oneBaseExtension_holomorphic (j : Kind) (θ : Form FamilyModel Threefold.Space 1) :
    ContMDiff I₁ I₁ ω (oneBaseExtension j θ) :=
  ((baseJacobian_holomorphic j).inv₀ (baseJacobian_ne_zero j)).mul
    (oneBaseCoefficient.contMDiff.comp (globalCoverZeroCoefficients_holomorphic j θ))

/-- Exactly the additional hypothesis required in source Lemma 9.16(i):
after the genuine global fibre coefficient is zero, the base coefficient extends. -/
theorem oneBaseExtension_eq_of_fibre_zero (j : Kind)
    (θ : Form FamilyModel Threefold.Space 1)
    (hc : ∀ z : TriangleRegularPoint, RegularCover.fibreOne θ z = 0) (z : RootStar j) :
    oneBaseExtension j θ z.val = RegularCover.baseOne θ (regularBase j z) := by
  have hc' : oneFibreCoefficient (regularCoverPullback j θ (gaugePoint j (z, 0))) = 0 :=
    (regularCover_oneFibre j θ (gaugePoint j (z, 0))).trans (hc (regularBase j z))
  have he : oneBaseCoefficient (globalCoverZeroCoefficients j θ z.val) =
      baseJacobian j z.val * RegularCover.baseOne θ (regularBase j z) := by
    rw [globalCoverZeroCoefficients_apply, globalCoverNativeCoefficients_eq]
    change oneBaseCoefficient (globalCoverPullback j θ (starCoverInclusion j (z, 0))) = _
    exact (oneBaseCoefficient_gauge_of_fibre_zero j θ (z, 0) hc').trans
      (regularCover_oneBase j θ (gaugePoint j (z, 0)))
  change (baseJacobian j z.val)⁻¹ * oneBaseCoefficient (globalCoverZeroCoefficients j θ z.val) = _
  rw [he, ← mul_assoc, inv_mul_cancel₀ (baseJacobian_ne_zero j z.val), one_mul]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover
