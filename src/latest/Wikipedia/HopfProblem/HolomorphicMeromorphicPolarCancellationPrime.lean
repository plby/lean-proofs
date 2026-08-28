import Mathlib.Algebra.Prime.Lemmas

/-!
# Prime-power cancellation without unique factorization

In a cancellative commutative monoid with zero, a prime that does not
divide the proposed divisor can be removed from the other side of a
divisibility statement, one factor at a time. A unit factor does not
change divisibility either.
-/

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarCancellation

variable {B : Type*} [CommMonoidWithZero B] [IsCancelMulZero B]
  {t q h : B}

/-- A power of a prime not dividing `q` can be cancelled from a multiple
of `q`; no factorization hypothesis on the ambient monoid is needed. -/
theorem dvd_of_dvd_mul_prime_pow (ht : Prime t) (htq : ¬t ∣ q) (n : ℕ)
    (hdiv : q ∣ h * t ^ n) : q ∣ h := by
  revert hdiv
  induction n with
  | zero =>
      intro hdiv
      simpa only [pow_zero, mul_one] using hdiv
  | succ n ih =>
      intro hdiv
      rw [pow_succ', mul_left_comm] at hdiv
      exact ih ((ht.left_dvd_or_dvd_right_of_dvd_mul hdiv).resolve_left htq)

/-- Prime-power cancellation also allows a unit in the multiplied factor. -/
theorem dvd_of_dvd_mul_prime_pow_unit (ht : Prime t) (htq : ¬t ∣ q) (n : ℕ)
    (u : Bˣ) (hdiv : q ∣ h * (t ^ n * (u : B))) : q ∣ h := by
  have hdiv' : q ∣ (h * t ^ n) * (u : B) := by
    simpa only [mul_assoc] using hdiv
  exact dvd_of_dvd_mul_prime_pow ht htq n (Units.dvd_mul_right.mp hdiv')

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarCancellation
