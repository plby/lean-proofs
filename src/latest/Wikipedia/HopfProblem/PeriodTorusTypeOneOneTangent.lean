import Wikipedia.HopfProblem.PeriodTori
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneCoordinates

/-!
# Integral coefficient forms on the actual period-torus tangent model

The real period isomorphism is the one used to construct the genuine
period lattice and quotient torus. Pulling each integral alternating form
through its inverse gives a real alternating form on the actual covering
tangent space `ℂ²`. No Néron–Severi or cohomological comparison is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

open scoped Matrix

/-- The actual real period isomorphism, in the ordered lattice marking. -/
def periodEquiv (p : PeriodDomain) : (Fin 4 → ℝ) ≃ₗ[ℝ] ComplexPlane₂ :=
  p.realEquiv.trans complexCoordinates

theorem periodEquiv_coordinates (p : PeriodDomain) (v : Fin 4 → ℝ) :
    periodEquiv p v =
      ![6 * p.val.μ * (v 0) + p.val.τ * (v 1) + (v 2),
        p.val.β * (v 0) + p.val.μ * (v 1) + (v 3)] := by
  change complexCoordinates (p.realEquiv v) = _
  rw [PeriodDomain.realEquiv_apply]
  ext i : 1
  fin_cases i <;> apply Complex.ext <;>
    simp [complexCoordinates, PeriodPoint.realMatrix, dotProduct,
      Fin.sum_univ_four, Complex.mul_re, Complex.mul_im]

/-- The real period map carries the standard basis to the actual period columns. -/
theorem periodEquiv_single (p : PeriodDomain) (j : Fin 4) :
    periodEquiv p (Pi.single j 1) = p.basis j := by
  simp only [PeriodDomain.basis, Module.Basis.map_apply, Pi.basisFun_apply]
  rfl

/-- The genuine real alternating form on the tangent model of the period torus. -/
def tangentForm (p : PeriodDomain) (E : Fin 6 → ℤ) :
    LinearMap.BilinForm ℝ ComplexPlane₂ :=
  (coordinateForm (fun k => (E k : ℝ))).compl₁₂
    (periodEquiv p).symm.toLinearMap (periodEquiv p).symm.toLinearMap

@[simp] theorem tangentForm_apply (p : PeriodDomain) (E : Fin 6 → ℤ)
    (x y : ComplexPlane₂) :
    tangentForm p E x y =
      coordinateForm (fun k => (E k : ℝ)) ((periodEquiv p).symm x) ((periodEquiv p).symm y) := rfl

/-- Pullback to the actual period coordinates recovers the given form exactly. -/
@[simp] theorem tangentForm_periodEquiv (p : PeriodDomain) (E : Fin 6 → ℤ)
    (x y : Fin 4 → ℝ) :
    tangentForm p E (periodEquiv p x) (periodEquiv p y) =
      coordinateForm (fun k => (E k : ℝ)) x y := by
  simp only [tangentForm_apply, LinearEquiv.symm_apply_apply]

theorem tangentForm_self (p : PeriodDomain) (E : Fin 6 → ℤ) (x : ComplexPlane₂) :
    tangentForm p E x x = 0 := by
  rw [tangentForm_apply]
  exact coordinateForm_self _ _

theorem tangentForm_swap (p : PeriodDomain) (E : Fin 6 → ℤ) (x y : ComplexPlane₂) :
    tangentForm p E x y = -tangentForm p E y x := by
  rw [tangentForm_apply, tangentForm_apply]
  exact coordinateForm_swap _ _ _

/-- The form has exactly the prescribed integral values on every named period-column pair. -/
theorem tangentForm_basis_pair (p : PeriodDomain) (E : Fin 6 → ℤ) (k : Fin 6) :
    tangentForm p E (p.basis (coefficientPair k).1) (p.basis (coefficientPair k).2) =
      (E k : ℝ) := by
  rw [← periodEquiv_single, ← periodEquiv_single, tangentForm_periodEquiv]
  exact coordinateForm_basis_pair _ k

/-- Every integral period combination has an integral pairing with every other. -/
theorem tangentForm_integer_periods (p : PeriodDomain) (E : Fin 6 → ℤ)
    (x y : Fin 4 → ℤ) :
    tangentForm p E (periodEquiv p (fun i => (x i : ℝ)))
        (periodEquiv p (fun i => (y i : ℝ))) = (coordinateForm E x y : ℝ) := by
  rw [tangentForm_periodEquiv]
  simp [coordinateForm_apply, coordinateValue]

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
