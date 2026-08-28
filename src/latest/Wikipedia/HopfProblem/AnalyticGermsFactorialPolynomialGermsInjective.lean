import Wikipedia.HopfProblem.AnalyticGermsFactorialPolynomialGerms
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Injectivity of polynomials with actual analytic-germ coefficients

The one-variable discrete valuation factorization lets us divide a nonzero
polynomial by the smallest coordinate power occurring among its nonzero
coefficients. The resulting polynomial has nonzero reduction at the origin.
This coefficient argument supplies injectivity of the realization of such
polynomials as actual two-variable analytic germs.
-/

noncomputable section

open Polynomial
open Wikipedia.HopfProblem.CuspNormalization.Germs.CoordinateDivision

namespace Wikipedia.HopfProblem.CuspNormalization.Germs.PolynomialGerms

/-- Removing the least coordinate power from the coefficients leaves a polynomial
whose coefficientwise evaluation at the origin is nonzero. -/
theorem exists_eq_C_centeredCoordinateGerm_pow_mul
    (P : Polynomial (AnalyticGerm (0 : ℂ))) (hP : P ≠ 0) :
    ∃ (n : ℕ) (Q : Polynomial (AnalyticGerm (0 : ℂ))),
      P = C (centeredCoordinateGerm 0) ^ n * Q ∧ Q.map (eval (0 : ℂ)) ≠ 0 := by
  classical
  have hcoeff : ∃ i, P.coeff i ≠ 0 := by
    by_contra! h
    apply hP
    apply Polynomial.ext
    intro i
    simpa only [coeff_zero] using h i
  have hex : ∃ n : ℕ, ∃ i : ℕ, ∃ u : (AnalyticGerm (0 : ℂ))ˣ,
      P.coeff i = centeredCoordinateGerm 0 ^ n * u := by
    obtain ⟨i, hi⟩ := hcoeff
    obtain ⟨n, u, hu⟩ := exists_eq_centeredCoordinateGerm_pow_mul_unit (P.coeff i) hi
    exact ⟨n, i, u, hu⟩
  let n := Nat.find hex
  obtain ⟨i, u, hi⟩ := Nat.find_spec hex
  have hdiv : C (centeredCoordinateGerm 0 ^ n) ∣ P := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro j
    by_cases hj : P.coeff j = 0
    · simp [hj]
    obtain ⟨m, v, hv⟩ := exists_eq_centeredCoordinateGerm_pow_mul_unit (P.coeff j) hj
    have hnm : n ≤ m := Nat.find_min' hex ⟨j, v, hv⟩
    rw [hv]
    exact dvd_mul_of_dvd_left (pow_dvd_pow _ hnm) _
  obtain ⟨Q, hQ⟩ := hdiv
  refine ⟨n, Q, ?_, ?_⟩
  · simpa only [map_pow] using hQ
  · have hQi : Q.coeff i = (u : AnalyticGerm (0 : ℂ)) := by
      apply mul_left_cancel₀ (pow_ne_zero n (centeredCoordinateGerm_ne_zero 0))
      calc
        centeredCoordinateGerm 0 ^ n * Q.coeff i = P.coeff i := by
          rw [hQ, coeff_C_mul]
        _ = centeredCoordinateGerm 0 ^ n * u := hi
    intro hmap
    have hz := congrArg (fun R : Polynomial ℂ => R.coeff i) hmap
    have huv : eval (0 : ℂ) (u : AnalyticGerm (0 : ℂ)) = 0 := by
      simpa only [coeff_map, coeff_zero, hQi] using hz
    exact (u.isUnit.map (eval (0 : ℂ))).ne_zero huv

/-- A nonzero polynomial with one-variable germ coefficients has a nonzero
actual two-variable germ. -/
theorem polynomialGerm_ne_zero (P : Polynomial O₁) (hP : P ≠ 0) :
    polynomialGerm P ≠ 0 := by
  obtain ⟨n, Q, hPQ, hQ⟩ := exists_eq_C_centeredCoordinateGerm_pow_mul P hP
  have hQimage : polynomialGerm Q ≠ 0 := by
    intro hz
    apply hQ
    apply (firstCoordinateGerm_dvd_polynomialGerm_iff Q).mp
    rw [hz]
    exact dvd_zero _
  rw [hPQ, map_mul, map_pow, polynomialGerm_C, fstPullback_centeredCoordinateGerm]
  exact mul_ne_zero (pow_ne_zero n firstCoordinateGerm_ne_zero) hQimage

/-- Polynomial realization in the actual two-variable analytic-germ ring is injective. -/
theorem polynomialGerm_injective : Function.Injective polynomialGerm := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro P hP
  by_contra hzero
  exact polynomialGerm_ne_zero P hzero hP

@[simp] theorem polynomialGerm_eq_zero_iff (P : Polynomial O₁) :
    polynomialGerm P = 0 ↔ P = 0 := by
  constructor
  · intro h
    apply polynomialGerm_injective
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero _

end Wikipedia.HopfProblem.CuspNormalization.Germs.PolynomialGerms
