import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsCoefficients
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsDerivatives

/-!
# Coefficient normal forms for actual holomorphic period maps

The period translations and their derivatives in these statements are
the actual maps of the period family, not supplied lattice or derivative
data. The two constant identity columns discharge the fixed-period
conditions in the full-lattice calculation.
-/

noncomputable section

open Set
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms

variable {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

local instance periodMapProductChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (B × ComplexPlane₂))

variable (P : HolomorphicPeriodMap ℂ B)

/-- One-form coefficient normal form for the genuine varying periods. -/
theorem oneForm_normal_form
    {a : B × ComplexPlane₂ → ℂ} {c : B × ComplexPlane₂ → ComplexPlane₂}
    (ha : ContMDiff I₃ I₁ ω a) (hc : ContMDiff I₃ I₂ ω c)
    (hcper : ∀ b ell ζ, c (b, ζ + periodShift P b ell) = c (b, ζ))
    (haper : ∀ b ell ζ, a (b, ζ + periodShift P b ell) +
      dotProduct (c (b, ζ + periodShift P b ell)) (periodDerivative P b ell) = a (b, ζ)) :
    ∃ A : B → ℂ, ∃ C : B → ComplexPlane₂,
      ContMDiff I₁ I₁ ω A ∧ ContMDiff I₁ I₂ ω C ∧
      (∀ b ζ, a (b, ζ) = A b ∧ c (b, ζ) = C b) ∧
      ∀ b ell, dotProduct (C b) (periodDerivative P b ell) = 0 := by
  apply oneForm_normal_form_of_period_laws P.point (periodDerivative P)
    (periodDerivative_single_two P) (periodDerivative_single_three P) ha hc
  · simpa only [periodShift_eq_periodVector] using hcper
  · simpa only [periodShift_eq_periodVector] using haper

/-- The vertical coefficient of a two-form vanishes when the actual
first-period derivative is nonzero on a dense subset of the base. -/
theorem twoForm_normal_form
    {a : B × ComplexPlane₂ → ℂ} {b : B × ComplexPlane₂ → ComplexPlane₂}
    (ha : ContMDiff I₃ I₁ ω a) (hb : ContMDiff I₃ I₂ ω b)
    (haper : ∀ z ell ζ, a (z, ζ + periodShift P z ell) = a (z, ζ))
    (hbper : ∀ z ell ζ, b (z, ζ + periodShift P z ell) +
      a (z, ζ + periodShift P z ell) • skewPeriod (periodDerivative P z ell) = b (z, ζ))
    (hDense : Dense {z : B |
      mfderiv I₁ I₁ (fun c => (P.point c).val.τ) z (1 : ℂ) ≠ 0}) :
    ∃ C : B → ComplexPlane₂, ContMDiff I₁ I₂ ω C ∧
      ∀ z ζ, a (z, ζ) = 0 ∧ b (z, ζ) = C z := by
  apply twoForm_normal_form_of_period_laws P.point (periodDerivative P)
    (periodDerivative_single_two P) (periodDerivative_single_three P) ha hb
  · simpa only [periodShift_eq_periodVector] using haper
  · simpa only [periodShift_eq_periodVector] using hbper
  · apply hDense.mono
    intro z hz heq
    exact hz ((periodDerivative_single_one_zero P z).symm.trans heq)

/-- A top-form coefficient is a holomorphic function on the actual base. -/
theorem threeForm_normal_form {c : B × ComplexPlane₂ → ℂ}
    (hc : ContMDiff I₃ I₁ ω c)
    (hcper : ∀ b ell ζ, c (b, ζ + periodShift P b ell) = c (b, ζ)) :
    ∃ C : B → ℂ, ContMDiff I₁ I₁ ω C ∧ ∀ b ζ, c (b, ζ) = C b := by
  apply threeForm_normal_form_of_period_laws P.point hc
  simpa only [periodShift_eq_periodVector] using hcper

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms
