import Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialFormsCoefficients
import Wikipedia.HopfProblem.HolomorphicDifferentialFormsCoordinateEvaluation

/-!
# Lemma 9.15 for arbitrary genuine local forms

An arbitrary holomorphic differential form on the original native special
period family over an open subset of the upper half-plane has the stated
base-dependent normal form after actual quotient pullback. All lattice
invariance and period-derivative conditions have been proved from the given
form and the constructed special periods. Connectedness of the open base
is unnecessary. The final formulas evaluate the entire actual covector.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms

open SpecialPeriods
open PeriodFamilyHolomorphicForms (periodDerivative specialPeriodPoint specialPeriodDerivative)

attribute [local instance] familyChartedSpace coverChartedSpace family_isManifold cover_isManifold

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

variable (U : TopologicalSpace.Opens UpperHalfPlane)

/-- Both actual one-form coefficients are independent of the fibre,
and the vertical row annihilates every original period derivative. -/
theorem oneForm_normal_form (θ : Form U 1) :
    (∀ z ζ, oneBase U θ (z, ζ) = baseOne U θ z ∧
      oneFibre U θ (z, ζ) = fibreOne U θ z) ∧
      ∀ z ℓ, dotProduct (fibreOne U θ z)
        (periodDerivative specialPeriodMap z.val ℓ) = 0 := by
  have hcper : ∀ z ℓ ζ,
      oneFibre U θ (z, ζ + (specialPeriodPoint U z).periodVector ℓ) =
        oneFibre U θ (z, ζ) := by
    intro z ℓ ζ
    simpa only [PeriodFamilyHolomorphicForms.periodShift_eq_periodVector,
      periods_point, specialPeriodPoint] using oneFibre_periodic U θ z ℓ ζ
  have haper : ∀ z ℓ ζ,
      oneBase U θ (z, ζ + (specialPeriodPoint U z).periodVector ℓ) +
        dotProduct (oneFibre U θ (z, ζ + (specialPeriodPoint U z).periodVector ℓ))
          (specialPeriodDerivative U z ℓ) = oneBase U θ (z, ζ) := by
    intro z ℓ ζ
    simpa only [PeriodFamilyHolomorphicForms.periodShift_eq_periodVector,
      periods_point, periodDerivative_eq, specialPeriodPoint, specialPeriodDerivative]
      using oneBase_period_law U θ z ℓ ζ
  obtain ⟨A, C, _, _, hval, hderiv⟩ :=
    PeriodFamilyHolomorphicForms.special_oneForm_normal_form U
      (oneBase_holomorphic U θ) (oneFibre_holomorphic U θ) hcper haper
  constructor
  · intro z ζ
    exact ⟨(hval z ζ).1.trans (hval z 0).1.symm,
      (hval z ζ).2.trans (hval z 0).2.symm⟩
  · intro z ℓ
    have hz : fibreOne U θ z = C z := (hval z 0).2
    rw [hz]
    exact hderiv z ℓ

theorem oneBase_eq_baseOne (θ : Form U 1) (z : U) (ζ : ComplexPlane₂) :
    oneBase U θ (z, ζ) = baseOne U θ z := ((oneForm_normal_form U θ).1 z ζ).1

theorem oneFibre_eq_fibreOne (θ : Form U 1) (z : U) (ζ : ComplexPlane₂) :
    oneFibre U θ (z, ζ) = fibreOne U θ z := ((oneForm_normal_form U θ).1 z ζ).2

theorem fibreOne_periodDerivative (θ : Form U 1) (z : U) (ℓ : Lattice) :
    dotProduct (fibreOne U θ z) (periodDerivative specialPeriodMap z.val ℓ) = 0 :=
  (oneForm_normal_form U θ).2 z ℓ

/-- The actual vertical-area coefficient vanishes, and the actual mixed
coefficients depend only on the base; nonvanishing of tau's derivative
on a dense set is supplied by the constructed special periods. -/
theorem twoForm_normal_form (θ : Form U 2) :
    ∀ z ζ, twoVertical U θ (z, ζ) = 0 ∧ twoMixed U θ (z, ζ) = mixedTwo U θ z := by
  have haper : ∀ z ℓ ζ,
      twoVertical U θ (z, ζ + (specialPeriodPoint U z).periodVector ℓ) =
        twoVertical U θ (z, ζ) := by
    intro z ℓ ζ
    simpa only [PeriodFamilyHolomorphicForms.periodShift_eq_periodVector,
      periods_point, specialPeriodPoint] using twoVertical_periodic U θ z ℓ ζ
  have hbper : ∀ z ℓ ζ,
      twoMixed U θ (z, ζ + (specialPeriodPoint U z).periodVector ℓ) +
        twoVertical U θ (z, ζ + (specialPeriodPoint U z).periodVector ℓ) •
          PeriodFamilyHolomorphicForms.skewPeriod (specialPeriodDerivative U z ℓ) =
        twoMixed U θ (z, ζ) := by
    intro z ℓ ζ
    simpa only [PeriodFamilyHolomorphicForms.periodShift_eq_periodVector,
      periods_point, periodDerivative_eq, specialPeriodPoint, specialPeriodDerivative]
      using twoMixed_period_law U θ z ℓ ζ
  obtain ⟨C, _, hval⟩ :=
    PeriodFamilyHolomorphicForms.special_twoForm_normal_form U
      (twoVertical_holomorphic U θ) (twoMixed_holomorphic U θ) haper hbper
  intro z ζ
  exact ⟨(hval z ζ).1, (hval z ζ).2.trans (hval z 0).2.symm⟩

theorem twoVertical_eq_zero (θ : Form U 2) (z : U) (ζ : ComplexPlane₂) :
    twoVertical U θ (z, ζ) = 0 := (twoForm_normal_form U θ z ζ).1

theorem twoMixed_eq_mixedTwo (θ : Form U 2) (z : U) (ζ : ComplexPlane₂) :
    twoMixed U θ (z, ζ) = mixedTwo U θ z := (twoForm_normal_form U θ z ζ).2

/-- The coefficient of every genuine local top form depends only on the base. -/
theorem top_eq_baseTop (θ : Form U 3) (z : U) (ζ : ComplexPlane₂) :
    top U θ (z, ζ) = baseTop U θ z := by
  have hcper : ∀ z ℓ ζ,
      top U θ (z, ζ + (specialPeriodPoint U z).periodVector ℓ) = top U θ (z, ζ) := by
    intro z ℓ ζ
    simpa only [PeriodFamilyHolomorphicForms.periodShift_eq_periodVector,
      periods_point, specialPeriodPoint] using top_periodic U θ z ℓ ζ
  obtain ⟨C, _, hval⟩ :=
    PeriodFamilyHolomorphicForms.special_threeForm_normal_form U (top_holomorphic U θ) hcper
  exact (hval z ζ).trans (hval z 0).symm

/-- The full actual quotient-pulled one-covector has the source normal form. -/
theorem oneForm_evaluation (θ : Form U 1) (z : U) (ζ : ComplexPlane₂) (u : Model) :
    coverPullback U θ (z, ζ) ![u] =
      baseOne U θ z * u.1 + dotProduct (fibreOne U θ z) u.2 := by
  have h := HolomorphicDifferentialForms.Coordinates.one_evaluation
    (nativeCoefficients U θ (z, ζ)) u
  rw [nativeCoefficients_apply] at h
  change coverPullback U θ (z, ζ) ![u] =
    oneBase U θ (z, ζ) * u.1 + dotProduct (oneFibre U θ (z, ζ)) u.2 at h
  simpa only [oneBase_eq_baseOne, oneFibre_eq_fibreOne] using h

/-- The full actual two-covector is the wedge of the base differential
with a holomorphic row of original fibre differentials. -/
theorem twoForm_evaluation (θ : Form U 2) (z : U) (ζ : ComplexPlane₂) (u v : Model) :
    coverPullback U θ (z, ζ) ![u, v] =
      u.1 * dotProduct (mixedTwo U θ z) v.2 -
        v.1 * dotProduct (mixedTwo U θ z) u.2 := by
  have h := HolomorphicDifferentialForms.Coordinates.two_evaluation
    (nativeCoefficients U θ (z, ζ)) u v
  rw [nativeCoefficients_apply] at h
  change coverPullback U θ (z, ζ) ![u, v] =
    twoVertical U θ (z, ζ) * (u.2 0 * v.2 1 - u.2 1 * v.2 0) +
      u.1 * dotProduct (twoMixed U θ (z, ζ)) v.2 -
        v.1 * dotProduct (twoMixed U θ (z, ζ)) u.2 at h
  simpa only [twoVertical_eq_zero, twoMixed_eq_mixedTwo, zero_mul, zero_add] using h

/-- The full actual top covector is a holomorphic base scalar times the
original oriented coordinate volume. -/
theorem threeForm_evaluation (θ : Form U 3) (z : U) (ζ : ComplexPlane₂) (u v w : Model) :
    coverPullback U θ (z, ζ) ![u, v, w] =
      baseTop U θ z * PeriodFamilyHolomorphicForms.coordinateVolume u v w := by
  have h := HolomorphicDifferentialForms.Coordinates.top_evaluation
    (nativeCoefficients U θ (z, ζ)) u v w
  rw [nativeCoefficients_apply] at h
  change coverPullback U θ (z, ζ) ![u, v, w] =
    top U θ (z, ζ) * PeriodFamilyHolomorphicForms.coordinateVolume u v w at h
  simpa only [top_eq_baseTop] using h

/-- Lemma 9.15(a), for arbitrary genuine local forms and every open base,
including the original period-derivative annihilation relation. -/
theorem exists_oneForm_normal_form (θ : Form U 1) :
    ∃ a : U → ℂ, ∃ c : U → ComplexPlane₂,
      ContMDiff I₁ I₁ ω a ∧ ContMDiff I₁ I₂ ω c ∧
      (∀ z ζ u, coverPullback U θ (z, ζ) ![u] =
        a z * u.1 + dotProduct (c z) u.2) ∧
      ∀ z ℓ, dotProduct (c z) (periodDerivative specialPeriodMap z.val ℓ) = 0 :=
  ⟨baseOne U θ, fibreOne U θ, baseOne_holomorphic U θ, fibreOne_holomorphic U θ,
    oneForm_evaluation U θ, fibreOne_periodDerivative U θ⟩

/-- Lemma 9.15(b), without a periodicity or genericity premise on the form. -/
theorem exists_twoForm_normal_form (θ : Form U 2) :
    ∃ b : U → ComplexPlane₂, ContMDiff I₁ I₂ ω b ∧
      ∀ z ζ u v, coverPullback U θ (z, ζ) ![u, v] =
        u.1 * dotProduct (b z) v.2 - v.1 * dotProduct (b z) u.2 :=
  ⟨mixedTwo U θ, mixedTwo_holomorphic U θ, twoForm_evaluation U θ⟩

/-- Lemma 9.15(c), for the genuine native quotient family over any open base. -/
theorem exists_threeForm_normal_form (θ : Form U 3) :
    ∃ c : U → ℂ, ContMDiff I₁ I₁ ω c ∧
      ∀ z ζ u v w, coverPullback U θ (z, ζ) ![u, v, w] =
        c z * PeriodFamilyHolomorphicForms.coordinateVolume u v w :=
  ⟨baseTop U θ, baseTop_holomorphic U θ, threeForm_evaluation U θ⟩

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms
