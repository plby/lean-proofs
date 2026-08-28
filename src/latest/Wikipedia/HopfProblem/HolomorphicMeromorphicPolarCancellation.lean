import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarCancellationPrime
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarAlgebraBasic
import Mathlib.Tactic.Ring

/-!
# Denominator principality from a prime-power scalar Bézout relation

Let `t` be prime in a domain, with `t ∤ q`. A relation
`A * p + C * q = t ^ n * u`, where `u` is a unit, suffices to cancel `p`
from divisibility by `q`. The actual denominator ideal of `p / q` is
therefore `(q)`.

No unique-factorization hypothesis is imposed on this domain. The scalar
relation is explicit algebraic input; neither its analytic existence nor
any global polar construction is asserted here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarCancellation

open PolarAlgebra

variable {B : Type*} [CommRing B] [IsDomain B] {t p q : B}

/-- A single explicit prime-power Bézout relation proves the required
cancellation, without factoriality of the ring. -/
theorem dvd_of_dvd_mul_of_bezout_eq_prime_power
    (ht : Prime t) (htq : ¬ t ∣ q) (n : ℕ) (u : Bˣ) (A C : B)
    (hbez : A * p + C * q = t ^ n * (u : B))
    (h : B) (hdiv : q ∣ h * p) : q ∣ h := by
  apply dvd_of_dvd_mul_prime_pow_unit ht htq n u
  have he : h * (t ^ n * (u : B)) = A * (h * p) + (h * C) * q := by
    rw [← hbez]
    ring
  rw [he]
  exact dvd_add (dvd_mul_of_dvd_right hdiv A) (dvd_mul_left q (h * C))

/-- Existence of the displayed scalar relation gives cancellation for
every multiplier `h`. No nonzero-numerator condition is required. -/
theorem dvd_of_dvd_mul_of_bezout_prime_power
    (ht : Prime t) (htq : ¬ t ∣ q)
    (hbez : ∃ n : ℕ, ∃ u : Bˣ, ∃ A C : B, A * p + C * q = t ^ n * (u : B))
    (h : B) (hdiv : q ∣ h * p) : q ∣ h := by
  obtain ⟨n, u, A, C, he⟩ := hbez
  exact dvd_of_dvd_mul_of_bezout_eq_prime_power ht htq n u A C he h hdiv

theorem dvd_mul_iff_of_bezout_prime_power
    (ht : Prime t) (htq : ¬ t ∣ q)
    (hbez : ∃ n : ℕ, ∃ u : Bˣ, ∃ A C : B, A * p + C * q = t ^ n * (u : B))
    (h : B) : q ∣ h * p ↔ q ∣ h :=
  ⟨dvd_of_dvd_mul_of_bezout_prime_power ht htq hbez h,
    fun hd => dvd_mul_of_dvd_left hd p⟩

/-- The scalar may first be exhibited separately and then factored as
a power of the prime times a unit. -/
theorem dvd_of_dvd_mul_of_bezout_scalar
    (ht : Prime t) (htq : ¬ t ∣ q) {a : B}
    (hbez : ∃ A C : B, A * p + C * q = a)
    (ha : ∃ n : ℕ, ∃ u : Bˣ, a = t ^ n * (u : B))
    (h : B) (hdiv : q ∣ h * p) : q ∣ h := by
  obtain ⟨A, C, he⟩ := hbez
  obtain ⟨n, u, ha⟩ := ha
  exact dvd_of_dvd_mul_of_bezout_eq_prime_power ht htq n u A C (he.trans ha) h hdiv

variable {K : Type*} [Field K] [Algebra B K] [IsFractionRing B K]

/-- The explicit scalar Bézout relation makes the literal denominator
ideal principal even when no UFD structure on `B` is available. -/
theorem denominatorIdeal_eq_span_of_bezout_prime_power
    (ht : Prime t) (htq : ¬ t ∣ q)
    (hbez : ∃ n : ℕ, ∃ u : Bˣ, ∃ A C : B, A * p + C * q = t ^ n * (u : B)) :
    denominatorIdeal B (algebraMap B K p / algebraMap B K q) =
      Ideal.span ({q} : Set B) := by
  have hq : q ≠ 0 := by
    rintro rfl
    exact htq (dvd_zero t)
  ext h
  rw [mem_denominatorIdeal_div_iff B p q hq, Ideal.mem_span_singleton]
  exact dvd_mul_iff_of_bezout_prime_power ht htq hbez h

theorem denominatorIdeal_eq_span_of_bezout_eq_prime_power
    (ht : Prime t) (htq : ¬ t ∣ q) (n : ℕ) (u : Bˣ) (A C : B)
    (hbez : A * p + C * q = t ^ n * (u : B)) :
    denominatorIdeal B (algebraMap B K p / algebraMap B K q) =
      Ideal.span ({q} : Set B) :=
  denominatorIdeal_eq_span_of_bezout_prime_power ht htq ⟨n, u, A, C, hbez⟩

/-- A separately identified prime-power scalar gives the same exact
denominator-ideal formula. -/
theorem denominatorIdeal_eq_span_of_bezout_scalar
    (ht : Prime t) (htq : ¬ t ∣ q) {a : B}
    (hbez : ∃ A C : B, A * p + C * q = a)
    (ha : ∃ n : ℕ, ∃ u : Bˣ, a = t ^ n * (u : B)) :
    denominatorIdeal B (algebraMap B K p / algebraMap B K q) =
      Ideal.span ({q} : Set B) := by
  obtain ⟨A, C, he⟩ := hbez
  obtain ⟨n, u, ha⟩ := ha
  exact denominatorIdeal_eq_span_of_bezout_eq_prime_power ht htq n u A C (he.trans ha)

/-- The corresponding actual principality instance, with no UFD input. -/
theorem denominatorIdeal_isPrincipal_of_bezout_prime_power
    (ht : Prime t) (htq : ¬ t ∣ q)
    (hbez : ∃ n : ℕ, ∃ u : Bˣ, ∃ A C : B, A * p + C * q = t ^ n * (u : B)) :
    (denominatorIdeal B (algebraMap B K p / algebraMap B K q)).IsPrincipal :=
  ⟨q, denominatorIdeal_eq_span_of_bezout_prime_power ht htq hbez⟩

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarCancellation
