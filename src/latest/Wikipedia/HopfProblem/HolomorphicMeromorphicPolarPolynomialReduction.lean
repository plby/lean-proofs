import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Polynomial reduction with unit leading coefficients

Over a factorial domain, removing a common polynomial factor preserves
unit leading coefficients of the common factor and reduced denominator
whenever the original denominator has unit leading coefficient.

This uses the actual polynomial unique-factorization instance; no
factorization hypothesis on any target ring is involved.
-/

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarPolynomial

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/-- Reduce a polynomial pair with unit-leading-coefficient denominator.
The common factor and reduced denominator still have unit leading
coefficients, including when the numerator is zero. -/
theorem exists_reduced_factors_unit_leadingCoeff (P Q : R[X])
    (hQ : IsUnit Q.leadingCoeff) :
    ∃ A D C : R[X], IsRelPrime A D ∧ C * A = P ∧ C * D = Q ∧
      IsUnit C.leadingCoeff ∧ IsUnit D.leadingCoeff := by
  have hQ0 : Q ≠ 0 := leadingCoeff_ne_zero.mp hQ.ne_zero
  obtain ⟨A, D, C, hAD, hP, hCD⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors' P Q hQ0
  have hprod : IsUnit (C.leadingCoeff * D.leadingCoeff) := by
    rw [← leadingCoeff_mul, hCD]
    exact hQ
  obtain ⟨hC, hD⟩ := IsUnit.mul_iff.mp hprod
  exact ⟨A, D, C, hAD, hP, hCD, hC, hD⟩

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarPolynomial
