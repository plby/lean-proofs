import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsPeriodLaws
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsSpecial

/-!
# Lemma 9.15 for genuine forms on the constructed threefold

Every coefficient below is extracted from the actual derivative
pullback of an arbitrary global holomorphic form. Its holomorphicity
and all period laws have already been proved from the native geometry.
Thus the normal forms have no periodicity, genericity or derivative
conditions as hypotheses.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

open HolomorphicDifferentialForms (Form)
open PeriodFamilyHolomorphicForms
  (periodShift periodDerivative specialPeriodPoint specialPeriodDerivative skewPeriod)

attribute [local instance] chartedSpace coverChartedSpace cover_isManifold space_isManifold

theorem periodPoint_eq (z : TriangleRegularPoint) :
    data.periods.point z = specialPeriodMap.point z.val := rfl

/-- Both coefficients of every actual one-form are independent of the
complex fibre vector; the vertical coefficient kills every period derivative. -/
theorem oneForm_normal_form (θ : Form Model Threefold.Space 1) :
    (∀ z ζ, oneBase θ (z, ζ) = baseOne θ z ∧ oneFibre θ (z, ζ) = fibreOne θ z) ∧
      ∀ z ℓ, dotProduct (fibreOne θ z) (periodDerivative specialPeriodMap z.val ℓ) = 0 := by
  have hcper : ∀ z ℓ ζ,
      oneFibre θ (z, ζ + (specialPeriodPoint triangleRegularDomain z).periodVector ℓ) =
        oneFibre θ (z, ζ) := by
    intro z ℓ ζ
    simpa only [PeriodFamilyHolomorphicForms.periodShift_eq_periodVector,
      periodPoint_eq, specialPeriodPoint] using oneFibre_periodic θ z ℓ ζ
  have haper : ∀ z ℓ ζ,
      oneBase θ (z, ζ + (specialPeriodPoint triangleRegularDomain z).periodVector ℓ) +
        dotProduct
          (oneFibre θ (z, ζ + (specialPeriodPoint triangleRegularDomain z).periodVector ℓ))
          (specialPeriodDerivative triangleRegularDomain z ℓ) = oneBase θ (z, ζ) := by
    intro z ℓ ζ
    simpa only [PeriodFamilyHolomorphicForms.periodShift_eq_periodVector,
      periodPoint_eq, periodDerivative_eq, specialPeriodPoint, specialPeriodDerivative]
      using oneBase_period_law θ z ℓ ζ
  obtain ⟨A, C, _, _, hval, hderiv⟩ :=
    PeriodFamilyHolomorphicForms.special_oneForm_normal_form triangleRegularDomain
      (oneBase_holomorphic θ) (oneFibre_holomorphic θ) hcper haper
  constructor
  · intro z ζ
    exact ⟨(hval z ζ).1.trans (hval z 0).1.symm,
      (hval z ζ).2.trans (hval z 0).2.symm⟩
  · intro z ℓ
    have hz : fibreOne θ z = C z := (hval z 0).2
    rw [hz]
    exact hderiv z ℓ

/-- The actual horizontal one-form coefficient is its zero-fibre value. -/
theorem oneBase_eq_baseOne (θ : Form Model Threefold.Space 1)
    (z : TriangleRegularPoint) (ζ : ComplexPlane₂) :
    oneBase θ (z, ζ) = baseOne θ z := (oneForm_normal_form θ).1 z ζ |>.1

/-- The actual vertical one-form coefficient is its zero-fibre value. -/
theorem oneFibre_eq_fibreOne (θ : Form Model Threefold.Space 1)
    (z : TriangleRegularPoint) (ζ : ComplexPlane₂) :
    oneFibre θ (z, ζ) = fibreOne θ z := (oneForm_normal_form θ).1 z ζ |>.2

theorem fibreOne_periodDerivative (θ : Form Model Threefold.Space 1)
    (z : TriangleRegularPoint) (ℓ : Lattice) :
    dotProduct (fibreOne θ z) (periodDerivative specialPeriodMap z.val ℓ) = 0 :=
  (oneForm_normal_form θ).2 z ℓ

/-- Every actual two-form has zero vertical-area coefficient and its
mixed coefficients are independent of the complex fibre vector. -/
theorem twoForm_normal_form (θ : Form Model Threefold.Space 2) :
    ∀ z ζ, twoVertical θ (z, ζ) = 0 ∧ twoMixed θ (z, ζ) = mixedTwo θ z := by
  have haper : ∀ z ℓ ζ,
      twoVertical θ (z, ζ + (specialPeriodPoint triangleRegularDomain z).periodVector ℓ) =
        twoVertical θ (z, ζ) := by
    intro z ℓ ζ
    simpa only [PeriodFamilyHolomorphicForms.periodShift_eq_periodVector,
      periodPoint_eq, specialPeriodPoint] using twoVertical_periodic θ z ℓ ζ
  have hbper : ∀ z ℓ ζ,
      twoMixed θ (z, ζ + (specialPeriodPoint triangleRegularDomain z).periodVector ℓ) +
        twoVertical θ (z, ζ + (specialPeriodPoint triangleRegularDomain z).periodVector ℓ) •
          skewPeriod (specialPeriodDerivative triangleRegularDomain z ℓ) =
        twoMixed θ (z, ζ) := by
    intro z ℓ ζ
    simpa only [PeriodFamilyHolomorphicForms.periodShift_eq_periodVector,
      periodPoint_eq, periodDerivative_eq, specialPeriodPoint, specialPeriodDerivative]
      using twoMixed_period_law θ z ℓ ζ
  obtain ⟨C, _, hval⟩ :=
    PeriodFamilyHolomorphicForms.special_twoForm_normal_form triangleRegularDomain
      (twoVertical_holomorphic θ) (twoMixed_holomorphic θ) haper hbper
  intro z ζ
  exact ⟨(hval z ζ).1, (hval z ζ).2.trans (hval z 0).2.symm⟩

theorem twoVertical_eq_zero (θ : Form Model Threefold.Space 2)
    (z : TriangleRegularPoint) (ζ : ComplexPlane₂) :
    twoVertical θ (z, ζ) = 0 := (twoForm_normal_form θ z ζ).1

theorem twoMixed_eq_mixedTwo (θ : Form Model Threefold.Space 2)
    (z : TriangleRegularPoint) (ζ : ComplexPlane₂) :
    twoMixed θ (z, ζ) = mixedTwo θ z := (twoForm_normal_form θ z ζ).2

/-- The actual three-form coefficient is independent of the complex fibre vector. -/
theorem top_eq_baseTop (θ : Form Model Threefold.Space 3)
    (z : TriangleRegularPoint) (ζ : ComplexPlane₂) : top θ (z, ζ) = baseTop θ z := by
  have hcper : ∀ z ℓ ζ,
      top θ (z, ζ + (specialPeriodPoint triangleRegularDomain z).periodVector ℓ) =
        top θ (z, ζ) := by
    intro z ℓ ζ
    simpa only [PeriodFamilyHolomorphicForms.periodShift_eq_periodVector,
      periodPoint_eq, specialPeriodPoint] using top_periodic θ z ℓ ζ
  obtain ⟨C, _, hval⟩ :=
    PeriodFamilyHolomorphicForms.special_threeForm_normal_form triangleRegularDomain
      (top_holomorphic θ) hcper
  exact (hval z ζ).trans (hval z 0).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
