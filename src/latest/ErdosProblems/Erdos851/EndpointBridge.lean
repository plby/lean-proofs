/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.LocalEulerProducts
import ErdosProblems.Erdos851.SieveSpecialization

/-!
# Endpoint alignment for the Erdős 851 sieve

The finite combinatorial sieve inherited from Erdős 387 uses primes in the
open interval `(z,Y)`.  The local Euler-product layer uses primes in the
half-open interval `(z,y]`.  Taking `Y = y + 1` makes these sets literally
equal.  This file records that equality and the resulting one- and two-shift
Euler-product identities.
-/

namespace Erdos851

open scoped BigOperators

/-- The open sieve interval `(z,y+1)` equals the half-open local-product
interval `(z,y]`. -/
theorem erdos387_sievePrimes_succ (z y : ℕ) :
    Erdos387.sievePrimes z (y + 1) = sievePrimes z y := by
  ext p
  simp only [Erdos387.mem_sievePrimes, mem_sievePrimes]
  constructor
  · rintro ⟨hp, hzp, hpy⟩
    exact ⟨hzp, by omega, hp⟩
  · rintro ⟨hzp, hpy, hp⟩
    exact ⟨hp, hzp, by omega⟩

/-- The corresponding products of sieving primes agree. -/
theorem erdos387_sievePrimeProduct_succ (z y : ℕ) :
    Erdos387.sievePrimeProduct z (y + 1) =
      ∏ p ∈ sievePrimes z y, p := by
  simp only [Erdos387.sievePrimeProduct, erdos387_sievePrimes_succ]

/-- The distinct prime factors of the sieve product are exactly the primes
in the local Euler interval. -/
theorem primeFactors_erdos387_sievePrimeProduct_succ (z y : ℕ) :
    (Erdos387.sievePrimeProduct z (y + 1)).primeFactors =
      sievePrimes z y := by
  rw [erdos387_sievePrimeProduct_succ]
  exact Nat.primeFactors_prod fun p hp ↦ (mem_sievePrimes.mp hp).2.2

/-- Congruence of two shifts modulo `p` is divisibility of their natural
distance by `p`. -/
theorem mod_eq_iff_dvd_dist (s t p : ℕ) :
    s % p = t % p ↔ p ∣ Nat.dist s t := by
  by_cases hst : s ≤ t
  · rw [Nat.dist_eq_sub_of_le hst]
    exact Nat.modEq_iff_dvd' hst
  · have hts : t ≤ s := by omega
    rw [Nat.dist_eq_sub_of_le_right hts]
    simpa [Nat.ModEq, eq_comm] using (Nat.modEq_iff_dvd' hts :
      t % p = s % p ↔ p ∣ s - t)

/-- A singleton shift has the one-shift local density at every prime. -/
theorem shiftNu_singleton_prime (s : ℕ) {p : ℕ} (hp : p.Prime) :
    ShiftSieve.shiftNu {s} p = oneShiftDensity p := by
  rw [ShiftSieve.shiftNu_prime hp, ShiftSieve.localNu_singleton]
  simp [oneShiftDensity, div_eq_mul_inv]

/-- A pair of shifts has density `1/p` when the prime divides their
difference and `2/p` otherwise. -/
theorem shiftNu_pair_prime (s t : ℕ) {p : ℕ} (hp : p.Prime) :
    ShiftSieve.shiftNu {s, t} p = pairShiftDensity (Nat.dist s t) p := by
  rw [ShiftSieve.shiftNu_prime hp]
  simp only [pairShiftDensity]
  split_ifs with hdiv
  · have hmod : s % p = t % p := (mod_eq_iff_dvd_dist s t p).2 hdiv
    rw [(ShiftSieve.localNu_pair_eq_one_iff).2 hmod]
    simp [div_eq_mul_inv]
  · have hmod : s % p ≠ t % p := by
      intro heq
      exact hdiv ((mod_eq_iff_dvd_dist s t p).1 heq)
    rw [(ShiftSieve.localNu_pair_eq_two_iff).2 hmod]
    simp [div_eq_mul_inv]

/-- The abstract sieve's singleton local Euler product is the one-shift
Euler product with upper endpoint `y`. -/
theorem shiftNu_singleton_eulerProduct (s z y : ℕ) :
    (∏ p ∈ (Erdos387.sievePrimeProduct z (y + 1)).primeFactors,
        (1 - ShiftSieve.shiftNu {s} p)) =
      localEulerProduct oneShiftDensity z y := by
  rw [primeFactors_erdos387_sievePrimeProduct_succ]
  simp only [localEulerProduct]
  apply Finset.prod_congr rfl
  intro p hp
  rw [shiftNu_singleton_prime s (mem_sievePrimes.mp hp).2.2]

/-- The abstract sieve's two-shift local Euler product is the pair product
whose separation is the natural distance between the shifts. -/
theorem shiftNu_pair_eulerProduct (s t z y : ℕ) :
    (∏ p ∈ (Erdos387.sievePrimeProduct z (y + 1)).primeFactors,
        (1 - ShiftSieve.shiftNu {s, t} p)) =
      localEulerProduct (pairShiftDensity (Nat.dist s t)) z y := by
  rw [primeFactors_erdos387_sievePrimeProduct_succ]
  simp only [localEulerProduct]
  apply Finset.prod_congr rfl
  intro p hp
  rw [shiftNu_pair_prime s t (mem_sievePrimes.mp hp).2.2]

end Erdos851
