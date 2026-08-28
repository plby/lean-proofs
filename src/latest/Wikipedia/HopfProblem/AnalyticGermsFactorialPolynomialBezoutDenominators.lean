import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Localization.Integral

/-!
# Clearing polynomial Bézout denominators

A polynomial Bézout identity over a fraction field can be multiplied by a
nonzero common scalar denominator. This produces an identity over the
original domain with a nonzero constant polynomial on the right.
-/

open Polynomial
open scoped nonZeroDivisors

namespace Wikipedia.HopfProblem.AnalyticGermsFactorial.PolynomialBezout

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- Clear the two polynomial denominators in a fraction-field Bézout identity. -/
theorem exists_nonzero_scalar_bezout_of_isCoprime_map {P Q : R[X]}
    (h : IsCoprime (P.map (algebraMap R K)) (Q.map (algebraMap R K))) :
    ∃ a : R, a ≠ 0 ∧ ∃ U V : R[X], U * P + V * Q = C a := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨a, ha, hu⟩ := IsLocalization.integerNormalization_spec R⁰ u
  obtain ⟨b, hb, hv⟩ := IsLocalization.integerNormalization_spec R⁰ v
  rw [Algebra.smul_def, Polynomial.algebraMap_apply] at hu hv
  refine ⟨a * b,
    mul_ne_zero (nonZeroDivisors.ne_zero ha) (nonZeroDivisors.ne_zero hb),
    C b * IsLocalization.integerNormalization R⁰ u,
    C a * IsLocalization.integerNormalization R⁰ v, ?_⟩
  apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hu, hv,
    map_mul]
  calc
    C (algebraMap R K b) * (C (algebraMap R K a) * u) * P.map (algebraMap R K) +
        C (algebraMap R K a) * (C (algebraMap R K b) * v) * Q.map (algebraMap R K) =
      C (algebraMap R K a) * C (algebraMap R K b) *
        (u * P.map (algebraMap R K) + v * Q.map (algebraMap R K)) := by ring
    _ = C (algebraMap R K a) * C (algebraMap R K b) := by rw [huv, mul_one]

end Wikipedia.HopfProblem.AnalyticGermsFactorial.PolynomialBezout
