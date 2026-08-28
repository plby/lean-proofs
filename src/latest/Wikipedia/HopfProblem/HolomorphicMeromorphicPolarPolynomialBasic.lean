import Wikipedia.HopfProblem.AnalyticGermsFactorialPolynomialBezout
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarCancellation
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Polynomial scalar Bézout identities in a target domain

Relatively prime polynomials over the coefficient UFD have an actual
nonzero scalar Bézout relation. A ring homomorphism sends that relation
to the target ring. When nonzero scalars become prime powers times units,
and unit-leading-coefficient polynomials avoid that prime, the denominator
ideal of a reduced polynomial fraction has its expected generator.

The target ring is not assumed to be a UFD. The two structural properties
of the homomorphism are explicit inputs, not analytic conclusions.
-/

noncomputable section

open Polynomial

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarPolynomial

open PolarAlgebra

variable {R B : Type*} [CommRing R] [CommRing B]
  (F : R[X] →+* B) {t : B}

/-- Avoidance of the prime also proves that these polynomial images
are nonzero, without assuming that the homomorphism is injective. -/
theorem image_ne_zero_of_isUnit_leadingCoeff
    (hprimitive : ∀ Q : R[X], IsUnit Q.leadingCoeff → ¬ t ∣ F Q)
    (Q : R[X]) (hQ : IsUnit Q.leadingCoeff) : F Q ≠ 0 := by
  intro hzero
  apply hprimitive Q hQ
  rw [hzero]
  exact dvd_zero t

section CommonFactor

variable {K : Type*} [Field K] [Algebra B K] [IsFractionRing B K]

/-- A nonzero common factor can be cancelled in the target fraction field. -/
theorem fraction_eq_of_common_factor {c p q p' q' : B}
    (hc : c ≠ 0) (hp : c * p' = p) (hq : c * q' = q) :
    algebraMap B K p / algebraMap B K q =
      algebraMap B K p' / algebraMap B K q' := by
  have hcK : algebraMap B K c ≠ 0 :=
    (map_ne_zero_iff (algebraMap B K) (IsFractionRing.injective B K)).mpr hc
  rw [← hp, ← hq]
  simp only [map_mul]
  rw [mul_div_mul_comm, div_self hcK, one_mul]

/-- Cancellation of a common polynomial factor is justified by its
nonzero image in the actual target fraction field. -/
theorem image_fraction_eq_of_common_factor (P Q A D C : R[X])
    (hP : C * A = P) (hQ : C * D = Q) (hC : F C ≠ 0) :
    algebraMap B K (F P) / algebraMap B K (F Q) =
      algebraMap B K (F A) / algebraMap B K (F D) :=
  fraction_eq_of_common_factor hC
    ((F.map_mul C A).symm.trans (congrArg F hP))
    ((F.map_mul C D).symm.trans (congrArg F hQ))

end CommonFactor

variable [IsDomain R] [UniqueFactorizationMonoid R]

/-- The genuine polynomial scalar Bézout identity maps to the required
prime-power-times-unit relation in the target ring. -/
theorem image_bezout_prime_power
    (hscalar : ∀ a : R, a ≠ 0 → ∃ n : ℕ, ∃ u : Bˣ,
      F (Polynomial.C a) = t ^ n * (u : B))
    {P Q : R[X]} (hpq : IsRelPrime P Q) :
    ∃ n : ℕ, ∃ u : Bˣ, ∃ A C : B,
      A * F P + C * F Q = t ^ n * (u : B) := by
  obtain ⟨a, ha, U, V, hUV⟩ :=
    AnalyticGermsFactorial.PolynomialBezout.exists_nonzero_scalar_bezout_of_isRelPrime hpq
  obtain ⟨n, u, hu⟩ := hscalar a ha
  refine ⟨n, u, F U, F V, ?_⟩
  calc
    F U * F P + F V * F Q = F (U * P + V * Q) := by
      rw [map_add, map_mul, map_mul]
    _ = F (Polynomial.C a) := congrArg F hUV
    _ = t ^ n * (u : B) := hu

variable [IsDomain B] {K : Type*} [Field K] [Algebra B K] [IsFractionRing B K]

/-- A reduced polynomial fraction has the literal image of its
denominator as a generator, without unique factorization in `B`. -/
theorem denominatorIdeal_eq_span_of_isRelPrime
    (ht : Prime t)
    (hscalar : ∀ a : R, a ≠ 0 → ∃ n : ℕ, ∃ u : Bˣ,
      F (Polynomial.C a) = t ^ n * (u : B))
    (hprimitive : ∀ Q : R[X], IsUnit Q.leadingCoeff → ¬ t ∣ F Q)
    {P Q : R[X]} (hpq : IsRelPrime P Q) (hQ : IsUnit Q.leadingCoeff) :
    denominatorIdeal B (algebraMap B K (F P) / algebraMap B K (F Q)) =
      Ideal.span ({F Q} : Set B) :=
  PolarCancellation.denominatorIdeal_eq_span_of_bezout_prime_power ht
    (hprimitive Q hQ) (image_bezout_prime_power F hscalar hpq)

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarPolynomial
