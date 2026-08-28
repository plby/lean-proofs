import Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms

/-!
# Actual coefficients and period laws of local family forms

These coefficients are evaluations of the derivative pullback of an
arbitrary genuine form on the native special-period family over an open
base. Their analyticity and every period law are proved from that form.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms

open HolomorphicDifferentialForms.Coordinates
open PeriodFamilyHolomorphicForms (periodShift periodDerivative skewPeriod)

attribute [local instance] familyChartedSpace coverChartedSpace family_isManifold cover_isManifold

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ Model

variable (U : TopologicalSpace.Opens UpperHalfPlane)

/-- The actual coefficient of the base differential. -/
def oneBase (θ : Form U 1) (x : Cover U) : ℂ :=
  oneBaseCoefficient (nativeCoefficients U θ x)

/-- The actual coefficients of the two original fibre differentials. -/
def oneFibre (θ : Form U 1) (x : Cover U) : ComplexPlane₂ :=
  oneFibreCoefficient (nativeCoefficients U θ x)

/-- The actual coefficient of the oriented vertical two-form. -/
def twoVertical (θ : Form U 2) (x : Cover U) : ℂ :=
  twoVerticalCoefficient (nativeCoefficients U θ x)

/-- The actual two mixed base-fibre coefficients. -/
def twoMixed (θ : Form U 2) (x : Cover U) : ComplexPlane₂ :=
  twoMixedCoefficient (nativeCoefficients U θ x)

/-- The coefficient of the original base-first three-dimensional volume. -/
def top (θ : Form U 3) (x : Cover U) : ℂ :=
  topCoefficient (nativeCoefficients U θ x)

theorem oneBase_holomorphic (θ : Form U 1) : ContMDiff IF I₁ ω (oneBase U θ) :=
  oneBaseCoefficient.contMDiff.comp (nativeCoefficients_holomorphic U θ)

theorem oneFibre_holomorphic (θ : Form U 1) : ContMDiff IF I₂ ω (oneFibre U θ) :=
  oneFibreCoefficient.contMDiff.comp (nativeCoefficients_holomorphic U θ)

theorem twoVertical_holomorphic (θ : Form U 2) : ContMDiff IF I₁ ω (twoVertical U θ) :=
  twoVerticalCoefficient.contMDiff.comp (nativeCoefficients_holomorphic U θ)

theorem twoMixed_holomorphic (θ : Form U 2) : ContMDiff IF I₂ ω (twoMixed U θ) :=
  twoMixedCoefficient.contMDiff.comp (nativeCoefficients_holomorphic U θ)

theorem top_holomorphic (θ : Form U 3) : ContMDiff IF I₁ ω (top U θ) :=
  topCoefficient.contMDiff.comp (nativeCoefficients_holomorphic U θ)

/-- Restriction of the actual base one-form coefficient to the zero section. -/
def baseOne (θ : Form U 1) (z : U) : ℂ := oneBase U θ (z, 0)

/-- Restriction of the actual vertical one-form coefficients to the zero section. -/
def fibreOne (θ : Form U 1) (z : U) : ComplexPlane₂ := oneFibre U θ (z, 0)

/-- Restriction of the actual mixed two-form coefficients to the zero section. -/
def mixedTwo (θ : Form U 2) (z : U) : ComplexPlane₂ := twoMixed U θ (z, 0)

/-- Restriction of the actual top coefficient to the zero section. -/
def baseTop (θ : Form U 3) (z : U) : ℂ := top U θ (z, 0)

theorem baseOne_holomorphic (θ : Form U 1) : ContMDiff I₁ I₁ ω (baseOne U θ) :=
  PeriodFamilyHolomorphicForms.zeroSectionRestriction_holomorphic (oneBase_holomorphic U θ)

theorem fibreOne_holomorphic (θ : Form U 1) : ContMDiff I₁ I₂ ω (fibreOne U θ) :=
  PeriodFamilyHolomorphicForms.zeroSectionRestriction_holomorphic (oneFibre_holomorphic U θ)

theorem mixedTwo_holomorphic (θ : Form U 2) : ContMDiff I₁ I₂ ω (mixedTwo U θ) :=
  PeriodFamilyHolomorphicForms.zeroSectionRestriction_holomorphic (twoMixed_holomorphic U θ)

theorem baseTop_holomorphic (θ : Form U 3) : ContMDiff I₁ I₁ ω (baseTop U θ) :=
  PeriodFamilyHolomorphicForms.zeroSectionRestriction_holomorphic (top_holomorphic U θ)

/-- The genuine local form proves periodicity of its actual vertical coefficients. -/
theorem oneFibre_periodic (θ : Form U 1) (z : U) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    oneFibre U θ (z, ζ + periodShift (periods U) z ℓ) = oneFibre U θ (z, ζ) :=
  HolomorphicDifferentialForms.PeriodLaws.oneFibre_periodic (periods U)
    (coverPullback U θ) (coverPullback_isPeriodInvariant U θ) z ℓ ζ

/-- The actual horizontal correction contains the original period derivative. -/
theorem oneBase_period_law (θ : Form U 1) (z : U) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    oneBase U θ (z, ζ + periodShift (periods U) z ℓ) +
      dotProduct (oneFibre U θ (z, ζ + periodShift (periods U) z ℓ))
        (periodDerivative (periods U) z ℓ) = oneBase U θ (z, ζ) :=
  HolomorphicDifferentialForms.PeriodLaws.oneBase_period_law (periods U)
    (coverPullback U θ) (coverPullback_isPeriodInvariant U θ) z ℓ ζ

theorem twoVertical_periodic (θ : Form U 2) (z : U) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    twoVertical U θ (z, ζ + periodShift (periods U) z ℓ) = twoVertical U θ (z, ζ) :=
  HolomorphicDifferentialForms.PeriodLaws.twoVertical_periodic (periods U)
    (coverPullback U θ) (coverPullback_isPeriodInvariant U θ) z ℓ ζ

/-- The actual alternating shear gives the mixed two-form correction. -/
theorem twoMixed_period_law (θ : Form U 2) (z : U) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    twoMixed U θ (z, ζ + periodShift (periods U) z ℓ) +
      twoVertical U θ (z, ζ + periodShift (periods U) z ℓ) •
        skewPeriod (periodDerivative (periods U) z ℓ) = twoMixed U θ (z, ζ) :=
  HolomorphicDifferentialForms.PeriodLaws.twoMixed_period_law (periods U)
    (coverPullback U θ) (coverPullback_isPeriodInvariant U θ) z ℓ ζ

theorem top_periodic (θ : Form U 3) (z : U) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    top U θ (z, ζ + periodShift (periods U) z ℓ) = top U θ (z, ζ) :=
  HolomorphicDifferentialForms.PeriodLaws.top_periodic (periods U)
    (coverPullback U θ) (coverPullback_isPeriodInvariant U θ) z ℓ ζ

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms
