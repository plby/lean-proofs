import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarPolynomialBasic
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarPolynomialReduction
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarPolynomialUnits

/-!
# Principal denominator ideals of polynomial images

Polynomial reduction takes place only over the coefficient UFD `R`.
The target ring `B` is merely a domain. The two stated structural facts
about `F : R[X] →+* B` supply a prime-power scalar Bézout relation and
avoidance of the distinguished prime by the reduced denominator.

The public witnesses retain actual target-ring elements, their common
factor, and the transferred Bézout identity. A separate divisibility
criterion does not require any fraction field. Actual units multiplying
the numerator and denominator do not change the denominator ideal.
No analytic preparation, factoriality of `B`, or global polar construction
is assumed as a conclusion here.
-/

noncomputable section

open Polynomial

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarPolynomial

open PolarAlgebra

variable {R B : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  [CommRing B] (F : R[X] →+* B) {t : B}

/-- Actual reduced image data, retaining the nonzero common factor and
the scalar Bézout relation for later local arguments. -/
theorem exists_reduced_image_data
    (hscalar : ∀ a : R, a ≠ 0 → ∃ n : ℕ, ∃ u : Bˣ,
      F (Polynomial.C a) = t ^ n * (u : B))
    (hprimitive : ∀ Q : R[X], IsUnit Q.leadingCoeff → ¬ t ∣ F Q)
    (P Q : R[X]) (hQ : IsUnit Q.leadingCoeff) :
    ∃ p' q' c : B, c ≠ 0 ∧ q' ≠ 0 ∧ ¬ t ∣ q' ∧
      c * p' = F P ∧ c * q' = F Q ∧
      ∃ n : ℕ, ∃ u : Bˣ, ∃ A C : B, A * p' + C * q' = t ^ n * (u : B) := by
  obtain ⟨A, D, C, hAD, hCA, hCD, hC, hD⟩ :=
    exists_reduced_factors_unit_leadingCoeff P Q hQ
  refine ⟨F A, F D, F C,
    image_ne_zero_of_isUnit_leadingCoeff F hprimitive C hC,
    image_ne_zero_of_isUnit_leadingCoeff F hprimitive D hD,
    hprimitive D hD, ?_, ?_, image_bezout_prime_power F hscalar hAD⟩
  · exact (F.map_mul C A).symm.trans (congrArg F hCA)
  · exact (F.map_mul C D).symm.trans (congrArg F hCD)

variable [IsDomain B]

/-- A purely ring-theoretic cancellation divisor, with no fraction-field
transport and no UFD assumption on the target ring. -/
theorem exists_cancellation_divisor
    (ht : Prime t)
    (hscalar : ∀ a : R, a ≠ 0 → ∃ n : ℕ, ∃ u : Bˣ,
      F (Polynomial.C a) = t ^ n * (u : B))
    (hprimitive : ∀ Q : R[X], IsUnit Q.leadingCoeff → ¬ t ∣ F Q)
    (P Q : R[X]) (hQ : IsUnit Q.leadingCoeff) :
    ∃ d : B, d ≠ 0 ∧ ¬ t ∣ d ∧ ∀ h : B, F Q ∣ h * F P ↔ d ∣ h := by
  obtain ⟨p', q', c, hc, hq', htq', hp, hq, hbez⟩ :=
    exists_reduced_image_data F hscalar hprimitive P Q hQ
  refine ⟨q', hq', htq', fun h => ?_⟩
  rw [← hp, ← hq, mul_left_comm h c p', mul_dvd_mul_iff_left hc]
  exact PolarCancellation.dvd_mul_iff_of_bezout_prime_power ht htq' hbez h

variable {K : Type*} [Field K] [Algebra B K] [IsFractionRing B K]

omit [IsDomain B] in
/-- The public reduced target-ring pair retains the exact fraction
equality, prime avoidance, and a genuine prime-power Bézout relation. -/
theorem exists_reduced_image_pair
    (hscalar : ∀ a : R, a ≠ 0 → ∃ n : ℕ, ∃ u : Bˣ,
      F (Polynomial.C a) = t ^ n * (u : B))
    (hprimitive : ∀ Q : R[X], IsUnit Q.leadingCoeff → ¬ t ∣ F Q)
    (P Q : R[X]) (hQ : IsUnit Q.leadingCoeff) :
    ∃ p' q' : B, q' ≠ 0 ∧ ¬ t ∣ q' ∧
      (∃ n : ℕ, ∃ u : Bˣ, ∃ A C : B, A * p' + C * q' = t ^ n * (u : B)) ∧
      algebraMap B K (F P) / algebraMap B K (F Q) =
        algebraMap B K p' / algebraMap B K q' := by
  obtain ⟨p', q', c, hc, hq', htq', hp, hq, hbez⟩ :=
    exists_reduced_image_data F hscalar hprimitive P Q hQ
  exact ⟨p', q', hq', htq', hbez, fraction_eq_of_common_factor hc hp hq⟩

/-- A nonzero target-ring generator of the actual denominator ideal. -/
theorem exists_denominator_generator_of_isUnit_leadingCoeff
    (ht : Prime t)
    (hscalar : ∀ a : R, a ≠ 0 → ∃ n : ℕ, ∃ u : Bˣ,
      F (Polynomial.C a) = t ^ n * (u : B))
    (hprimitive : ∀ Q : R[X], IsUnit Q.leadingCoeff → ¬ t ∣ F Q)
    (P Q : R[X]) (hQ : IsUnit Q.leadingCoeff) :
    ∃ d : B, d ≠ 0 ∧ ¬ t ∣ d ∧
      denominatorIdeal B (algebraMap B K (F P) / algebraMap B K (F Q)) =
        Ideal.span ({d} : Set B) := by
  obtain ⟨d, hd, htd, hdiv⟩ := exists_cancellation_divisor F ht hscalar hprimitive P Q hQ
  refine ⟨d, hd, htd, ?_⟩
  ext h
  rw [mem_denominatorIdeal_div_iff B (F P) (F Q)
    (image_ne_zero_of_isUnit_leadingCoeff F hprimitive Q hQ), Ideal.mem_span_singleton]
  exact hdiv h

/-- Unit leading coefficient of the denominator is sufficient; the
numerator is arbitrary and may vanish. -/
theorem denominatorIdeal_isPrincipal_of_isUnit_leadingCoeff
    (ht : Prime t)
    (hscalar : ∀ a : R, a ≠ 0 → ∃ n : ℕ, ∃ u : Bˣ,
      F (Polynomial.C a) = t ^ n * (u : B))
    (hprimitive : ∀ Q : R[X], IsUnit Q.leadingCoeff → ¬ t ∣ F Q)
    (P Q : R[X]) (hQ : IsUnit Q.leadingCoeff) :
    (denominatorIdeal B (algebraMap B K (F P) / algebraMap B K (F Q))).IsPrincipal := by
  obtain ⟨d, _, _, hd⟩ :=
    exists_denominator_generator_of_isUnit_leadingCoeff (K := K) F ht hscalar hprimitive P Q hQ
  exact ⟨d, hd⟩

/-- In particular, monic polynomial denominators give principal denominator ideals. -/
theorem denominatorIdeal_isPrincipal_of_monic
    (ht : Prime t)
    (hscalar : ∀ a : R, a ≠ 0 → ∃ n : ℕ, ∃ u : Bˣ,
      F (Polynomial.C a) = t ^ n * (u : B))
    (hprimitive : ∀ Q : R[X], IsUnit Q.leadingCoeff → ¬ t ∣ F Q)
    (P Q : R[X]) (hQ : Q.Monic) :
    (denominatorIdeal B (algebraMap B K (F P) / algebraMap B K (F Q))).IsPrincipal :=
  denominatorIdeal_isPrincipal_of_isUnit_leadingCoeff F ht hscalar hprimitive P Q
    (hQ.leadingCoeff.symm ▸ isUnit_one)

/-- Actual target-ring units on both entries preserve the same nonzero
denominator-ideal generator. -/
theorem exists_unit_fraction_denominator_generator
    (ht : Prime t)
    (hscalar : ∀ a : R, a ≠ 0 → ∃ n : ℕ, ∃ u : Bˣ,
      F (Polynomial.C a) = t ^ n * (u : B))
    (hprimitive : ∀ Q : R[X], IsUnit Q.leadingCoeff → ¬ t ∣ F Q)
    (P Q : R[X]) (hQ : IsUnit Q.leadingCoeff) (u v : Bˣ) :
    ∃ d : B, d ≠ 0 ∧ ¬ t ∣ d ∧
      denominatorIdeal B (algebraMap B K ((u : B) * F P) /
        algebraMap B K ((v : B) * F Q)) = Ideal.span ({d} : Set B) := by
  rw [denominatorIdeal_unit_mul_div_unit_mul]
  exact exists_denominator_generator_of_isUnit_leadingCoeff F ht hscalar hprimitive P Q hQ

theorem denominatorIdeal_isPrincipal_unit_factors
    (ht : Prime t)
    (hscalar : ∀ a : R, a ≠ 0 → ∃ n : ℕ, ∃ u : Bˣ,
      F (Polynomial.C a) = t ^ n * (u : B))
    (hprimitive : ∀ Q : R[X], IsUnit Q.leadingCoeff → ¬ t ∣ F Q)
    (P Q : R[X]) (hQ : IsUnit Q.leadingCoeff) (u v : Bˣ) :
    (denominatorIdeal B (algebraMap B K ((u : B) * F P) /
      algebraMap B K ((v : B) * F Q))).IsPrincipal := by
  rw [denominatorIdeal_unit_mul_div_unit_mul]
  exact denominatorIdeal_isPrincipal_of_isUnit_leadingCoeff F ht hscalar hprimitive P Q hQ

theorem denominatorIdeal_isPrincipal_monic_unit_factors
    (ht : Prime t)
    (hscalar : ∀ a : R, a ≠ 0 → ∃ n : ℕ, ∃ u : Bˣ,
      F (Polynomial.C a) = t ^ n * (u : B))
    (hprimitive : ∀ Q : R[X], IsUnit Q.leadingCoeff → ¬ t ∣ F Q)
    (P Q : R[X]) (hQ : Q.Monic) (u v : Bˣ) :
    (denominatorIdeal B (algebraMap B K ((u : B) * F P) /
      algebraMap B K ((v : B) * F Q))).IsPrincipal :=
  denominatorIdeal_isPrincipal_unit_factors F ht hscalar hprimitive P Q
    (hQ.leadingCoeff.symm ▸ isUnit_one) u v

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarPolynomial
