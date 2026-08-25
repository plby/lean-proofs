/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.PrimeProgressionSieve

/-!
# Expanding the shifted-coefficient prime-mass first moment

The B5 exceptional-set estimate begins by interchanging two finite sums.
This file records that identity with a named incidence set, so the remaining
number theory is exactly the reciprocal mass of cofactors on which one fixed
sieve prime divides the shifted coefficient.
-/

namespace Erdos822

open scoped BigOperators

/-- Odd raw cofactors whose shifted coefficient is divisible by a fixed
prime. -/
def shiftedDivisibleOddCofactors (N p : ℕ) : Finset ℕ :=
  (oddRawCofactors N).filter fun m => p ∣ shiftedTotient m

@[simp]
theorem mem_shiftedDivisibleOddCofactors_iff
    {N p m : ℕ} :
    m ∈ shiftedDivisibleOddCofactors N p ↔
      m ∈ oddRawCofactors N ∧ p ∣ shiftedTotient m := by
  simp [shiftedDivisibleOddCofactors]

/-- Weighted first moment of the truncated shifted-coefficient prime mass. -/
noncomputable def shiftedMassFirstMoment (N z y : ℕ) : ℝ :=
  ∑ m ∈ oddRawCofactors N,
    shiftedTotientReciprocalMass m z y / m

/-- Finite Fubini identity for the B5 first moment. -/
theorem shiftedMassFirstMoment_eq_prime_incidence_sum
    (N z y : ℕ) :
    shiftedMassFirstMoment N z y =
      ∑ p ∈ Erdos851.sievePrimes z y,
        ((1 : ℝ) / p) *
          ∑ m ∈ shiftedDivisibleOddCofactors N p,
            (1 : ℝ) / m := by
  unfold shiftedMassFirstMoment shiftedTotientReciprocalMass
  simp_rw [Finset.sum_div]
  calc
    (∑ m ∈ oddRawCofactors N,
        ∑ p ∈ Erdos851.sievePrimes z y,
          (if p ∣ shiftedTotient m then (1 : ℝ) / p else 0) / m) =
        ∑ m ∈ oddRawCofactors N,
          ∑ p ∈ Erdos851.sievePrimes z y,
            if p ∣ shiftedTotient m then
              ((1 : ℝ) / p) * ((1 : ℝ) / m) else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hpm : p ∣ shiftedTotient m
      · simp [hpm]
        ring
      · simp [hpm]
    _ = ∑ p ∈ Erdos851.sievePrimes z y,
          ∑ m ∈ oddRawCofactors N,
            if p ∣ shiftedTotient m then
              ((1 : ℝ) / p) * ((1 : ℝ) / m) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ Erdos851.sievePrimes z y,
          ((1 : ℝ) / p) *
            ∑ m ∈ shiftedDivisibleOddCofactors N p,
              (1 : ℝ) / m := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      unfold shiftedDivisibleOddCofactors
      rw [Finset.sum_filter]

/-- Any uniform reciprocal incidence estimate immediately gives a bound for
the full B5 first moment after summing over sieve primes. -/
theorem shiftedMassFirstMoment_le_of_incidence
    (N z y : ℕ) {D : ℝ}
    (hinc : ∀ p ∈ Erdos851.sievePrimes z y,
      ∑ m ∈ shiftedDivisibleOddCofactors N p,
        (1 : ℝ) / m ≤ D / p) :
    shiftedMassFirstMoment N z y ≤
      D * ∑ p ∈ Erdos851.sievePrimes z y,
        (1 : ℝ) / (p : ℝ) ^ 2 := by
  rw [shiftedMassFirstMoment_eq_prime_incidence_sum]
  calc
    (∑ p ∈ Erdos851.sievePrimes z y,
        ((1 : ℝ) / p) *
          ∑ m ∈ shiftedDivisibleOddCofactors N p,
            (1 : ℝ) / m) ≤
        ∑ p ∈ Erdos851.sievePrimes z y,
          ((1 : ℝ) / p) * (D / p) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hinc p hp) (by positivity)
    _ = D * ∑ p ∈ Erdos851.sievePrimes z y,
          (1 : ℝ) / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

end Erdos822
