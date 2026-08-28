import Wikipedia.HopfProblem.HolomorphicDifferentialFormsFlat
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsDerivatives
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticShearManifold
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticShearCoefficients

/-!
# Scalar period laws of genuine holomorphic differential forms

Translate the original complex fibre coordinates by the actual period
vector of a holomorphic period map. The native manifold derivative is
the shear determined by the actual period derivative. Invariance of a
genuine holomorphic form under this actual pullback therefore implies
all scalar one-, two-, and top-form period laws. No flat-chart condition
or independently supplied coefficient covariance is assumed.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.HolomorphicDifferentialForms.PeriodLaws

open Coordinates Coordinates.EllipticShear PeriodFamilyHolomorphicForms

variable {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ Model

local instance periodProductChartedSpace : ChartedSpace Model (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (B × ComplexPlane₂))

variable (P : HolomorphicPeriodMap ℂ B)

/-- The actual translation by the varying period with integral marking ℓ. -/
def periodTranslation (ℓ : Lattice) : (B × ComplexPlane₂) → B × ComplexPlane₂ :=
  gaugeTranslationOn (fun b => periodShift P b ℓ)

@[simp] theorem periodTranslation_apply (ℓ : Lattice) (x : B × ComplexPlane₂) :
    periodTranslation P ℓ x = (x.1, x.2 + periodShift P x.1 ℓ) := rfl

theorem periodTranslation_holomorphic (ℓ : Lattice) :
    ContMDiff IF IF ω (periodTranslation P ℓ) := by
  intro x
  exact contMDiffAt_gaugeTranslationOn (periodShift_holomorphic P ℓ x.1) x.2

/-- The shear vector is the genuine derivative of the original periods. -/
theorem mfderiv_periodTranslation (ℓ : Lattice) (b : B) (ζ : ComplexPlane₂) :
    mfderiv IF IF (periodTranslation P ℓ) (b, ζ) = shear (periodDerivative P b ℓ) :=
  mfderiv_gaugeTranslationOn ((periodShift_holomorphic P ℓ).mdifferentiable (by simp) b) ζ

variable [IsManifold I₁ ω B]

local instance periodProductManifold : IsManifold IF ω (B × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := I₁) (I' := I₂) B ComplexPlane₂

/-- Invariance means equality of genuine derivative pullbacks of the form. -/
def IsPeriodInvariant {p : ℕ} (η : Form Model (B × ComplexPlane₂) p) : Prop :=
  ∀ ℓ : Lattice,
    pullback (periodTranslation P ℓ) (periodTranslation_holomorphic P ℓ) η = η

/-- The actual form invariance gives the full native alternating-covector
identity, before any scalar coefficients are extracted. -/
theorem nativeCoefficients_periodTranslation {p : ℕ}
    (η : Form Model (B × ComplexPlane₂) p) (hη : IsPeriodInvariant P η)
    (b : B) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    (nativeCoefficients Model (B × ComplexPlane₂) η
        (b, ζ + periodShift P b ℓ)).compContinuousLinearMap (shear (periodDerivative P b ℓ)) =
      nativeCoefficients Model (B × ComplexPlane₂) η (b, ζ) := by
  have h := congrArg (fun θ : Form Model (B × ComplexPlane₂) p => θ (b, ζ)) (hη ℓ)
  rw [pullback_apply, mfderiv_periodTranslation, periodTranslation_apply] at h
  ext v
  change nativeCoefficients Model (B × ComplexPlane₂) η (b, ζ + periodShift P b ℓ)
      (fun i => shear (periodDerivative P b ℓ) (v i)) =
    nativeCoefficients Model (B × ComplexPlane₂) η (b, ζ) v
  rw [nativeCoefficients_apply, nativeCoefficients_apply]
  exact congrArg (fun a : Covector Model (B × ComplexPlane₂) p (b, ζ) => a v) h

/-- The actual horizontal coefficient of a genuine one-form. -/
def oneBase (η : Form Model (B × ComplexPlane₂) 1) (x : B × ComplexPlane₂) : ℂ :=
  oneBaseCoefficient (nativeCoefficients Model (B × ComplexPlane₂) η x)

/-- The actual two vertical coefficients of a genuine one-form. -/
def oneFibre (η : Form Model (B × ComplexPlane₂) 1) (x : B × ComplexPlane₂) :
    ComplexPlane₂ :=
  oneFibreCoefficient (nativeCoefficients Model (B × ComplexPlane₂) η x)

/-- The actual vertical-area coefficient of a genuine two-form. -/
def twoVertical (η : Form Model (B × ComplexPlane₂) 2) (x : B × ComplexPlane₂) : ℂ :=
  twoVerticalCoefficient (nativeCoefficients Model (B × ComplexPlane₂) η x)

/-- The actual two horizontal-vertical coefficients of a genuine two-form. -/
def twoMixed (η : Form Model (B × ComplexPlane₂) 2) (x : B × ComplexPlane₂) :
    ComplexPlane₂ :=
  twoMixedCoefficient (nativeCoefficients Model (B × ComplexPlane₂) η x)

/-- The actual coefficient of a genuine three-form. -/
def top (η : Form Model (B × ComplexPlane₂) 3) (x : B × ComplexPlane₂) : ℂ :=
  topCoefficient (nativeCoefficients Model (B × ComplexPlane₂) η x)

/-- Fibre coefficients of a genuine invariant one-form are exactly periodic. -/
theorem oneFibre_periodic (η : Form Model (B × ComplexPlane₂) 1)
    (hη : IsPeriodInvariant P η) (b : B) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    oneFibre η (b, ζ + periodShift P b ℓ) = oneFibre η (b, ζ) := by
  simpa only [oneFibre, oneFibreCoefficient_pullback] using
    congrArg oneFibreCoefficient (nativeCoefficients_periodTranslation P η hη b ℓ ζ)

/-- The horizontal one-form coefficient has its actual derivative correction. -/
theorem oneBase_period_law (η : Form Model (B × ComplexPlane₂) 1)
    (hη : IsPeriodInvariant P η) (b : B) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    oneBase η (b, ζ + periodShift P b ℓ) +
        dotProduct (oneFibre η (b, ζ + periodShift P b ℓ)) (periodDerivative P b ℓ) =
      oneBase η (b, ζ) := by
  simpa only [oneBase, oneFibre, oneBaseCoefficient_pullback] using
    congrArg oneBaseCoefficient (nativeCoefficients_periodTranslation P η hη b ℓ ζ)

/-- The vertical-area coefficient of a genuine invariant two-form is periodic. -/
theorem twoVertical_periodic (η : Form Model (B × ComplexPlane₂) 2)
    (hη : IsPeriodInvariant P η) (b : B) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    twoVertical η (b, ζ + periodShift P b ℓ) = twoVertical η (b, ζ) := by
  simpa only [twoVertical, twoVerticalCoefficient_pullback] using
    congrArg twoVerticalCoefficient (nativeCoefficients_periodTranslation P η hη b ℓ ζ)

/-- The mixed two-form coefficients have the genuine alternating shear correction. -/
theorem twoMixed_period_law (η : Form Model (B × ComplexPlane₂) 2)
    (hη : IsPeriodInvariant P η) (b : B) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    twoMixed η (b, ζ + periodShift P b ℓ) +
        twoVertical η (b, ζ + periodShift P b ℓ) • skewPeriod (periodDerivative P b ℓ) =
      twoMixed η (b, ζ) := by
  simpa only [twoMixed, twoVertical, twoMixedCoefficient_pullback] using
    congrArg twoMixedCoefficient (nativeCoefficients_periodTranslation P η hη b ℓ ζ)

/-- The genuine top-form coefficient is unchanged by every actual period translation. -/
theorem top_periodic (η : Form Model (B × ComplexPlane₂) 3)
    (hη : IsPeriodInvariant P η) (b : B) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    top η (b, ζ + periodShift P b ℓ) = top η (b, ζ) := by
  simpa only [top, topCoefficient_pullback] using
    congrArg topCoefficient (nativeCoefficients_periodTranslation P η hη b ℓ ζ)

/-- Both hypotheses of the scalar one-form normal-form theorem follow
from the single genuine-form invariance assertion. -/
theorem oneForm_period_laws (η : Form Model (B × ComplexPlane₂) 1)
    (hη : IsPeriodInvariant P η) :
    (∀ b ℓ ζ, oneFibre η (b, ζ + periodShift P b ℓ) = oneFibre η (b, ζ)) ∧
      ∀ b ℓ ζ, oneBase η (b, ζ + periodShift P b ℓ) +
          dotProduct (oneFibre η (b, ζ + periodShift P b ℓ)) (periodDerivative P b ℓ) =
        oneBase η (b, ζ) :=
  ⟨oneFibre_periodic P η hη, oneBase_period_law P η hη⟩

/-- Both period hypotheses of the scalar two-form normal-form theorem
follow from genuine-form invariance under the original translations. -/
theorem twoForm_period_laws (η : Form Model (B × ComplexPlane₂) 2)
    (hη : IsPeriodInvariant P η) :
    (∀ b ℓ ζ, twoVertical η (b, ζ + periodShift P b ℓ) = twoVertical η (b, ζ)) ∧
      ∀ b ℓ ζ, twoMixed η (b, ζ + periodShift P b ℓ) +
          twoVertical η (b, ζ + periodShift P b ℓ) • skewPeriod (periodDerivative P b ℓ) =
        twoMixed η (b, ζ) :=
  ⟨twoVertical_periodic P η hη, twoMixed_period_law P η hη⟩

end Wikipedia.HopfProblem.HolomorphicDifferentialForms.PeriodLaws
