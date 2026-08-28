import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsPeriodMap
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsUpperHalfPlane
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsTauRegular

/-!
# Lemma 9.15 for the actual special periods on every open base subset

The special periods have been constructed unconditionally. Their
first-period derivative is nonzero on the proved dense regular locus.
Consequently all three coefficient normal forms hold on any actual
open subset of the upper half-plane. The two-form statement has no
additional derivative or genericity premise.
-/

noncomputable section

open Set UpperHalfPlane
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms

open SpecialPeriods TriangleHolomorphicDifferentials

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

variable (U : TopologicalSpace.Opens ℍ)

local instance specialProductChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) (U × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (U × ComplexPlane₂))

/-- The already constructed admissible periods restricted to the open base. -/
def specialPeriodPoint (z : U) : PeriodDomain := specialPeriodMap.point z.val

/-- The actual period derivative in the inherited upper-half-plane coordinate. -/
def specialPeriodDerivative (z : U) (ell : Lattice) : ComplexPlane₂ :=
  periodDerivative specialPeriodMap z.val ell

@[simp] theorem specialPeriodDerivative_two (z : U) :
    specialPeriodDerivative U z (Pi.single 2 1) = 0 :=
  periodDerivative_single_two specialPeriodMap z.val

@[simp] theorem specialPeriodDerivative_three (z : U) :
    specialPeriodDerivative U z (Pi.single 3 1) = 0 :=
  periodDerivative_single_three specialPeriodMap z.val

/-- The indicated matrix entry is the genuine scalar derivative of the special tau. -/
theorem specialPeriodDerivative_tau (z : U) :
    specialPeriodDerivative U z (Pi.single 1 1) 0 = scalarDeriv specialTau z.val := by
  rw [specialPeriodDerivative, periodDerivative_single_one_zero]
  exact mfderiv_chart_scalar specialTau_holomorphic z.val

/-- The required nonvanishing set is dense in every open base subset. -/
theorem specialPeriodDerivative_nonzero_dense :
    Dense {z : U | specialPeriodDerivative U z (Pi.single 1 1) 0 ≠ 0} := by
  have hd : Dense ((Subtype.val : U → ℍ) ⁻¹'
      {z : ℍ | scalarDeriv specialTau z ≠ 0}) :=
    specialTau_scalarDeriv_nonzero_dense.preimage U.isOpen.isOpenMap_subtype_val
  apply hd.mono
  intro z hz hzero
  exact hz ((specialPeriodDerivative_tau U z).symm.trans hzero)

/-- The one-form coefficient normal form on the actual special family. -/
theorem special_oneForm_normal_form
    {a : U × ComplexPlane₂ → ℂ} {c : U × ComplexPlane₂ → ComplexPlane₂}
    (ha : ContMDiff I₃ I₁ ω a) (hc : ContMDiff I₃ I₂ ω c)
    (hcper : ∀ z ell ζ,
      c (z, ζ + (specialPeriodPoint U z).periodVector ell) = c (z, ζ))
    (haper : ∀ z ell ζ, a (z, ζ + (specialPeriodPoint U z).periodVector ell) +
      dotProduct (c (z, ζ + (specialPeriodPoint U z).periodVector ell))
        (specialPeriodDerivative U z ell) = a (z, ζ)) :
    ∃ A : U → ℂ, ∃ C : U → ComplexPlane₂,
      ContMDiff I₁ I₁ ω A ∧ ContMDiff I₁ I₂ ω C ∧
      (∀ z ζ, a (z, ζ) = A z ∧ c (z, ζ) = C z) ∧
      ∀ z ell, dotProduct (C z) (specialPeriodDerivative U z ell) = 0 :=
  oneForm_normal_form_of_period_laws (specialPeriodPoint U) (specialPeriodDerivative U)
    (specialPeriodDerivative_two U) (specialPeriodDerivative_three U) ha hc hcper haper

/-- The two-form coefficient normal form, with the tau derivative condition proved. -/
theorem special_twoForm_normal_form
    {a : U × ComplexPlane₂ → ℂ} {b : U × ComplexPlane₂ → ComplexPlane₂}
    (ha : ContMDiff I₃ I₁ ω a) (hb : ContMDiff I₃ I₂ ω b)
    (haper : ∀ z ell ζ,
      a (z, ζ + (specialPeriodPoint U z).periodVector ell) = a (z, ζ))
    (hbper : ∀ z ell ζ, b (z, ζ + (specialPeriodPoint U z).periodVector ell) +
      a (z, ζ + (specialPeriodPoint U z).periodVector ell) •
        skewPeriod (specialPeriodDerivative U z ell) = b (z, ζ)) :
    ∃ C : U → ComplexPlane₂, ContMDiff I₁ I₂ ω C ∧
      ∀ z ζ, a (z, ζ) = 0 ∧ b (z, ζ) = C z :=
  twoForm_normal_form_of_period_laws (specialPeriodPoint U) (specialPeriodDerivative U)
    (specialPeriodDerivative_two U) (specialPeriodDerivative_three U) ha hb haper hbper
    (specialPeriodDerivative_nonzero_dense U)

/-- The top-form coefficient normal form on the actual special family. -/
theorem special_threeForm_normal_form {c : U × ComplexPlane₂ → ℂ}
    (hc : ContMDiff I₃ I₁ ω c)
    (hcper : ∀ z ell ζ,
      c (z, ζ + (specialPeriodPoint U z).periodVector ell) = c (z, ζ)) :
    ∃ C : U → ℂ, ContMDiff I₁ I₁ ω C ∧ ∀ z ζ, c (z, ζ) = C z :=
  threeForm_normal_form_of_period_laws (specialPeriodPoint U) hc hcper

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms
