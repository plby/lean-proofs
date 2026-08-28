import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Relatively prime polynomials over a fraction field

Gauss's lemma carries relative primality over a GCD domain to its fraction
field. The target polynomial ring is a principal ideal domain, so relative
primality there gives a polynomial Bézout identity.
-/

open Polynomial
open scoped nonZeroDivisors

namespace Wikipedia.HopfProblem.AnalyticGermsFactorial.PolynomialBezout

variable {R K : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Relatively prime polynomials over a GCD domain remain relatively prime
after mapping their coefficients to a fraction field. -/
theorem isRelPrime_map_of_isRelPrime {P Q : R[X]} (h : IsRelPrime P Q) :
    IsRelPrime (P.map (algebraMap R K)) (Q.map (algebraMap R K)) := by
  let : NormalizedGCDMonoid R := Nonempty.some inferInstance
  intro D hDP hDQ
  have hD : D ≠ 0 := by
    intro hD0
    have hP : P = 0 := (Polynomial.map_eq_zero_iff (IsFractionRing.injective R K)).mp
      (zero_dvd_iff.mp (hD0 ▸ hDP))
    have hQ : Q = 0 := (Polynomial.map_eq_zero_iff (IsFractionRing.injective R K)).mp
      (zero_dvd_iff.mp (hD0 ▸ hDQ))
    exact not_isRelPrime_zero_zero (hP ▸ hQ ▸ h)
  let D' := IsLocalization.integerNormalization R⁰ D
  have hprim : D'.primPart.IsPrimitive := D'.isPrimitive_primPart
  have hmap : D'.primPart.map (algebraMap R K) ∣ D := by
    obtain ⟨b, hb, heq⟩ := IsLocalization.integerNormalization_spec R⁰ D
    have hdvd := Polynomial.map_dvd (algebraMap R K) D'.primPart_dvd
    change D'.primPart.map (algebraMap R K) ∣ D'.map (algebraMap R K) at hdvd
    rw [show D'.map (algebraMap R K) = b • D from heq,
      Algebra.smul_def, Polynomial.algebraMap_apply] at hdvd
    exact (IsUnit.dvd_mul_left
      (Polynomial.isUnit_C.mpr (IsLocalization.map_units K ⟨b, hb⟩))).mp hdvd
  have hunit : IsUnit D'.primPart := h
    (hprim.dvd_of_fraction_map_dvd_fraction_map (hmap.trans hDP))
    (hprim.dvd_of_fraction_map_dvd_fraction_map (hmap.trans hDQ))
  exact Polynomial.isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart hD hunit

/-- Relatively prime polynomials over a GCD domain have a polynomial Bézout
identity after mapping their coefficients to a fraction field. -/
theorem isCoprime_map_of_isRelPrime {P Q : R[X]} (h : IsRelPrime P Q) :
    IsCoprime (P.map (algebraMap R K)) (Q.map (algebraMap R K)) :=
  (isRelPrime_map_of_isRelPrime h).isCoprime

end Wikipedia.HopfProblem.AnalyticGermsFactorial.PolynomialBezout
