import Wikipedia.HopfProblem.AnalyticGermsFactorialPreparation
import Wikipedia.HopfProblem.AnalyticGermsFactorialCoordinatesRegular
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarPolynomial

/-!
# Principal denominator ideals in the genuine two-variable analytic ring

Two nonzero actual analytic germs are simultaneously made regular by an
actual linear coordinate change. Convergent preparation gives monic
polynomials over the proved one-variable discrete valuation ring. Genuine
polynomial reduction, a scalar Bézout identity, and primality of the first
coordinate then produce a principal denominator ideal.

The two-variable analytic ring is not assumed factorial or Noetherian.
This file proves the sufficient denominator-principality conclusion
directly, and transfers it through actual germ-ring coordinate equivalences.
-/

noncomputable section

open Set Filter Topology Polynomial
open Wikipedia.HopfProblem.CuspNormalization.Germs
open Wikipedia.HopfProblem.CuspNormalization.Germs.CoordinateDivision
open Wikipedia.HopfProblem.CuspNormalization.Germs.PolynomialGerms

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarPlane

open PolarAlgebra

/-- Nonzero one-variable coefficients become actual powers of the first
coordinate times units in the two-variable germ ring. -/
theorem coefficient_image_factorization (a : O₁) (ha : a ≠ 0) :
    ∃ n : ℕ, ∃ u : O₂ˣ,
      polynomialGerm (Polynomial.C a) = firstCoordinateGerm ^ n * (u : O₂) := by
  obtain ⟨n, u, hu⟩ := exists_eq_centeredCoordinateGerm_pow_mul_unit a ha
  refine ⟨n, Units.map fstPullback.toMonoidHom u, ?_⟩
  rw [polynomialGerm_C, hu, map_mul, map_pow, fstPullback_centeredCoordinateGerm]
  rfl

/-- Preparation of an actual germ whose second-axis restriction is nonzero. -/
theorem exists_preparation_of_axis_ne_zero (p : O₂) (hp : axisRestriction p ≠ 0) :
    ∃ P : Polynomial O₁, P.Monic ∧ ∃ u : O₂ˣ, p = polynomialGerm P * (u : O₂) := by
  obtain ⟨f, hf, rfl⟩ := exists_representative p
  apply AnalyticGermsFactorial.Preparation.exists_monic_polynomial_mul_unit hf
  intro hzero
  apply hp
  rw [axisRestriction_ofAnalytic, ofAnalytic_eq_zero_iff]
  exact hzero

/-- Actual prepared pairs have a cancellation divisor in the original
two-variable analytic-germ ring. -/
theorem exists_regular_cancellation_divisor (p q : O₂)
    (hp : axisRestriction p ≠ 0) (hq : axisRestriction q ≠ 0) :
    ∃ d : O₂, d ≠ 0 ∧ ∀ h : O₂, q ∣ h * p ↔ d ∣ h := by
  obtain ⟨P, hP, u, hpu⟩ := exists_preparation_of_axis_ne_zero p hp
  obtain ⟨Q, hQ, v, hqv⟩ := exists_preparation_of_axis_ne_zero q hq
  obtain ⟨d, hd, htd, hdiv⟩ := PolarPolynomial.exists_cancellation_divisor polynomialGerm
    firstCoordinateGerm_prime coefficient_image_factorization
    firstCoordinateGerm_not_dvd_polynomialGerm_of_isUnit_leadingCoeff
    P Q (hQ.leadingCoeff.symm ▸ isUnit_one)
  refine ⟨d, hd, fun h => ?_⟩
  rw [hpu, hqv, v.isUnit.mul_right_dvd, ← mul_assoc, u.isUnit.dvd_mul_right]
  exact hdiv h

/-- Ring equivalence transports the exact divisibility criterion, so no
fraction-field coordinate choices are required. -/
theorem cancellation_divisor_transport {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (p q : A)
    (h : ∃ d : B, d ≠ 0 ∧ ∀ a : B, e q ∣ a * e p ↔ d ∣ a) :
    ∃ d : A, d ≠ 0 ∧ ∀ a : A, q ∣ a * p ↔ d ∣ a := by
  obtain ⟨d, hd, hdiv⟩ := h
  refine ⟨e.symm d, by simpa using hd, fun a => ?_⟩
  calc
    q ∣ a * p ↔ e q ∣ e a * e p := by
      simpa only [map_mul] using (map_dvd_iff e (a := q) (b := a * p)).symm
    _ ↔ d ∣ e a := hdiv (e a)
    _ ↔ e.symm d ∣ a := by
      simpa only [RingEquiv.symm_apply_apply] using
        (map_dvd_iff e.symm (a := d) (b := e a)).symm

/-- Every pair of actual two-variable analytic germs has a principal
denominator-divisibility criterion. Both regularization and preparation
are constructed in the proof. -/
theorem exists_cancellation_divisor (p q : O₂) (hq : q ≠ 0) :
    ∃ d : O₂, d ≠ 0 ∧ ∀ h : O₂, q ∣ h * p ↔ d ∣ h := by
  by_cases hp : p = 0
  · exact ⟨1, one_ne_zero, fun h => by simp [hp]⟩
  obtain ⟨e, heP, heQ⟩ := Coordinates.exists_pair_regularizing_germ_coordinates p q hp hq
  apply cancellation_divisor_transport (Coordinates.linearPullbackEquiv e) p q
  exact exists_regular_cancellation_divisor _ _ heP heQ

/-- The criterion transfers to any ring actually isomorphic to this
analytic-germ ring. -/
theorem exists_cancellation_divisor_of_equiv {A : Type*} [CommRing A]
    (e : A ≃+* O₂) (p q : A) (hq : q ≠ 0) :
    ∃ d : A, d ≠ 0 ∧ ∀ h : A, q ∣ h * p ↔ d ∣ h :=
  cancellation_divisor_transport e p q
    (exists_cancellation_divisor (e p) (e q) (by simpa using hq))

/-- Actual analytic denominator ideals in any fraction field are principal.
There is no factoriality assumption on the two-variable local ring. -/
theorem denominatorIdeal_isPrincipal
    {K : Type*} [Field K] [Algebra O₂ K] [IsFractionRing O₂ K] (a : K) :
    (denominatorIdeal O₂ a).IsPrincipal := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective O₂ a
  obtain ⟨d, hd, hdiv⟩ := exists_cancellation_divisor p q (nonZeroDivisors.ne_zero hq)
  refine ⟨d, ?_⟩
  ext h
  rw [mem_denominatorIdeal_div_iff O₂ p q (nonZeroDivisors.ne_zero hq),
    Ideal.mem_span_singleton]
  exact hdiv h

/-- A coordinate-invariant version, suitable for the original categorical
holomorphic stalk via its proved chart equivalence. -/
theorem denominatorIdeal_isPrincipal_of_equiv
    {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (e : A ≃+* O₂) (a : K) :
    (denominatorIdeal A a).IsPrincipal := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective A a
  obtain ⟨d, hd, hdiv⟩ := exists_cancellation_divisor_of_equiv e p q
    (nonZeroDivisors.ne_zero hq)
  refine ⟨d, ?_⟩
  ext h
  rw [mem_denominatorIdeal_div_iff A p q (nonZeroDivisors.ne_zero hq),
    Ideal.mem_span_singleton]
  exact hdiv h

section Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Denominator principality at every point of any complex model with an
actual two-dimensional complex linear coordinate equivalence. -/
theorem analyticGerm_denominatorIdeal_isPrincipal
    (e : (ℂ × ℂ) ≃L[ℂ] E) (a : E)
    {K : Type*} [Field K] [Algebra (AnalyticGerm a) K]
    [IsFractionRing (AnalyticGerm a) K] (s : K) :
    (denominatorIdeal (AnalyticGerm a) s).IsPrincipal :=
  denominatorIdeal_isPrincipal_of_equiv (Coordinates.affinePullbackEquiv e 0 a) s

end Coordinates

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarPlane
