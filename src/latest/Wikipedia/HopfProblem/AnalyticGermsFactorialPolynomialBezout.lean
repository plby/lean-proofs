import Wikipedia.HopfProblem.AnalyticGermsFactorialPolynomialBezoutMap
import Wikipedia.HopfProblem.AnalyticGermsFactorialPolynomialBezoutDenominators
import Wikipedia.HopfProblem.AnalyticGermsFactorialOneVariable

/-!
# Scalar Bézout identities for relatively prime polynomials

Relatively prime polynomials over a GCD domain become coprime over its
fraction field. Clearing the coefficients of a field Bézout identity gives
a nonzero constant polynomial in their ideal. The scalar need not be a unit:
this does not assert that polynomial rings over PIDs are Bézout rings.

The final corollary applies this algebraic result to the already proved DVR
of actual analytic germs in one complex variable.
-/

open Polynomial
open Wikipedia.HopfProblem.CuspNormalization.Germs

namespace Wikipedia.HopfProblem.AnalyticGermsFactorial.PolynomialBezout

/-- Relative primality over a GCD domain gives a Bézout identity with a nonzero
scalar right-hand side. -/
theorem exists_nonzero_scalar_bezout_of_isRelPrime {R : Type*}
    [CommRing R] [IsDomain R] [IsGCDMonoid R] {P Q : R[X]}
    (h : IsRelPrime P Q) :
    ∃ a : R, a ≠ 0 ∧ ∃ U V : R[X], U * P + V * Q = C a :=
  exists_nonzero_scalar_bezout_of_isCoprime_map
    (isCoprime_map_of_isRelPrime (K := FractionRing R) h)

/-- The scalar Bézout identity for polynomials over actual one-variable
analytic germs, using their proved discrete valuation ring structure. -/
theorem exists_nonzero_analyticGerm_scalar_bezout {a : ℂ}
    {P Q : (AnalyticGerm a)[X]} (h : IsRelPrime P Q) :
    ∃ c : AnalyticGerm a, c ≠ 0 ∧
      ∃ U V : (AnalyticGerm a)[X], U * P + V * Q = C c :=
  exists_nonzero_scalar_bezout_of_isRelPrime h

end Wikipedia.HopfProblem.AnalyticGermsFactorial.PolynomialBezout
