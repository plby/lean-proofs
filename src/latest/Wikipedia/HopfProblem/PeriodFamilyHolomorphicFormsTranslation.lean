import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsCoefficients
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsTopCovariance

/-!
# Coefficient identities from the full period pullback evaluations

Each hypothesis below is the scalar evaluation of an entire covector
pullback identity under the actual period shear. Evaluating on coordinate
tangent vectors proves the coefficient identities used in Lemma 9.15.
No periodicity or coefficient normal form is assumed separately.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms

variable {B : Type*} (point : B → PeriodDomain) (d : B → Lattice → ComplexPlane₂)

/-- The full one-covector pullback identity gives both coefficient laws. -/
theorem oneForm_period_laws
    {a : B × ComplexPlane₂ → ℂ} {c : B × ComplexPlane₂ → ComplexPlane₂}
    (hpullback : ∀ z ell ζ v t,
      a (z, ζ + (point z).periodVector ell) * t +
        dotProduct (c (z, ζ + (point z).periodVector ell)) (v + t • d z ell) =
      a (z, ζ) * t + dotProduct (c (z, ζ)) v) :
    (∀ z ell ζ, c (z, ζ + (point z).periodVector ell) = c (z, ζ)) ∧
      ∀ z ell ζ, a (z, ζ + (point z).periodVector ell) +
        dotProduct (c (z, ζ + (point z).periodVector ell)) (d z ell) = a (z, ζ) := by
  constructor
  · intro z ell ζ
    funext i
    simpa only [mul_zero, zero_smul, add_zero, zero_add, dotProduct_single_one] using
      hpullback z ell ζ (Pi.single i 1) 0
  · intro z ell ζ
    simpa only [mul_one, one_smul, zero_add, dotProduct_zero, add_zero] using
      hpullback z ell ζ 0 1

/-- The full alternating two-covector pullback identity gives both coefficient laws. -/
theorem twoForm_period_laws
    {a : B × ComplexPlane₂ → ℂ} {b : B × ComplexPlane₂ → ComplexPlane₂}
    (hpullback : ∀ z ell ζ v w t s,
      let v' := v + t • d z ell
      let w' := w + s • d z ell
      a (z, ζ + (point z).periodVector ell) * (v' 0 * w' 1 - v' 1 * w' 0) +
        t * dotProduct (b (z, ζ + (point z).periodVector ell)) w' -
        s * dotProduct (b (z, ζ + (point z).periodVector ell)) v' =
      a (z, ζ) * (v 0 * w 1 - v 1 * w 0) +
        t * dotProduct (b (z, ζ)) w - s * dotProduct (b (z, ζ)) v) :
    (∀ z ell ζ, a (z, ζ + (point z).periodVector ell) = a (z, ζ)) ∧
      ∀ z ell ζ, b (z, ζ + (point z).periodVector ell) +
        a (z, ζ + (point z).periodVector ell) • skewPeriod (d z ell) = b (z, ζ) := by
  constructor
  · intro z ell ζ
    have h := hpullback z ell ζ (Pi.single (0 : Fin 2) 1) (Pi.single (1 : Fin 2) 1) 0 0
    dsimp only at h
    simpa using h
  · intro z ell ζ
    funext i
    have h := hpullback z ell ζ 0 (Pi.single i 1) 1 0
    dsimp only at h
    fin_cases i <;> simpa [skewPeriod, add_comm] using h

/-- A full top-covector period pullback identity makes its scalar coefficient periodic. -/
theorem threeForm_period_law {c : B × ComplexPlane₂ → ℂ}
    (hpullback : ∀ z ell ζ u v w,
      c (z, ζ + (point z).periodVector ell) * coordinateVolume
        (blockJacobian 1 1 (d z ell) u) (blockJacobian 1 1 (d z ell) v)
        (blockJacobian 1 1 (d z ell) w) = c (z, ζ) * coordinateVolume u v w) :
    ∀ z ell ζ, c (z, ζ + (point z).periodVector ell) = c (z, ζ) := by
  intro z ell ζ
  simpa only [coordinateVolume_periodShear, coordinateVolume_basis, mul_one] using
    hpullback z ell ζ (1, 0) (0, Pi.single (0 : Fin 2) 1) (0, Pi.single (1 : Fin 2) 1)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms
