/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.OddCofactorLayers

/-!
# Large common primes inside a structured cofactor

At the auxiliary cutoff N^4 a prime divisor of k*r*q cannot come from k.
It must be one of the two displayed prime layers.  This elementary
structure is the starting point for a direct retained-mass proof of a
large-cutoff B4 layer.
-/

namespace Erdos822

/-- A prime above N^4 dividing a structured cofactor is one of the two
displayed prime factors. -/
theorem prime_eq_middle_or_large_of_dvd_product_of_gt_pow_four
    {N p k r q : ℕ}
    (hN : 2 ≤ N)
    (hp : p.Prime) (hpN : N ^ 4 < p)
    (hk : k ∈ oddSmallFactors N)
    (hr : r ∈ middlePrimes N)
    (hq : q ∈ largePrimes N)
    (hpdvd : p ∣ k * r * q) :
    p = r ∨ p = q := by
  have hNk : k ≤ N := oddSmallFactors_le hk
  have hNN4 : N < N ^ 4 := by
    have hpow : N ^ 1 < N ^ 4 :=
      Nat.pow_lt_pow_right (by omega : 1 < N) (by omega)
    simpa using hpow
  have hpk : ¬ p ∣ k := by
    intro h
    have hpkle : p ≤ k := Nat.le_of_dvd (oddSmallFactors_pos hk) h
    omega
  have hrPrime : r.Prime := (mem_middlePrimes_iff.mp hr).2.2
  have hqPrime : q.Prime := (mem_largePrimes_iff.mp hq).2.2
  have hsplit : p ∣ k * r ∨ p ∣ q := hp.dvd_mul.mp hpdvd
  rcases hsplit with hkr | hpq
  · have hsplit' : p ∣ k ∨ p ∣ r := hp.dvd_mul.mp hkr
    rcases hsplit' with hpk' | hpr
    · exact False.elim (hpk hpk')
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp hrPrime).mp hpr)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp hqPrime).mp hpq)

/-- Totient of a structured cofactor, with the two new prime factors
displayed explicitly. -/
theorem totient_product_eq_of_oddCofactorTriple
    {N k r q : ℕ}
    (hN : 2 ≤ N)
    (hk : k ∈ oddSmallFactors N)
    (hr : r ∈ middlePrimes N)
    (hq : q ∈ largePrimes N) :
    Nat.totient (k * r * q) =
      (q - 1) * ((r - 1) * Nat.totient k) := by
  have hsep := oddCofactorTriples_separated hN
    (show (k, r, q) ∈ oddCofactorTriples N by
      rw [mem_oddCofactorTriples_iff]
      exact ⟨hk, hr, hq⟩)
  have hrPrime : r.Prime := (mem_middlePrimes_iff.mp hr).2.2
  have hqPrime : q.Prime := (mem_largePrimes_iff.mp hq).2.2
  have hrk : ¬ r ∣ k := by
    exact Nat.not_dvd_of_pos_of_lt (oddSmallFactors_pos hk) hsep.2.1
  have hqkr : ¬ q ∣ k * r := by
    exact Nat.not_dvd_of_pos_of_lt
      (Nat.mul_pos (oddSmallFactors_pos hk) hrPrime.pos) hsep.2.2
  rw [show k * r * q = q * (k * r) by ring,
    Nat.totient_mul_of_prime_of_not_dvd hqPrime hqkr]
  rw [show k * r = r * k by ring,
    Nat.totient_mul_of_prime_of_not_dvd hrPrime hrk]

/-- Above N^4, a prime common to a structured cofactor and its totient can
only be the middle-layer prime, and it then divides q-1. -/
theorem middle_dvd_large_pred_of_large_common_totient
    {N p k r q : ℕ}
    (hN : 2 ≤ N)
    (hp : p.Prime) (hpN : N ^ 4 < p)
    (hk : k ∈ oddSmallFactors N)
    (hr : r ∈ middlePrimes N)
    (hq : q ∈ largePrimes N)
    (hpm : p ∣ k * r * q)
    (hphi : p ∣ Nat.totient (k * r * q)) :
    r ∣ q - 1 := by
  have hsep := oddCofactorTriples_separated hN
    (show (k, r, q) ∈ oddCofactorTriples N by
      rw [mem_oddCofactorTriples_iff]
      exact ⟨hk, hr, hq⟩)
  have hkpos : 0 < k := oddSmallFactors_pos hk
  have hkN : k ≤ N := oddSmallFactors_le hk
  have hNN4 : N < N ^ 4 := by
    have hpow : N ^ 1 < N ^ 4 :=
      Nat.pow_lt_pow_right (by omega : 1 < N) (by omega)
    simpa using hpow
  have hrge : N ^ 4 ≤ r := (mem_middlePrimes_iff.mp hr).1
  have hrPrime : r.Prime := (mem_middlePrimes_iff.mp hr).2.2
  have hqPrime : q.Prime := (mem_largePrimes_iff.mp hq).2.2
  have hphiFormula :=
    totient_product_eq_of_oddCofactorTriple hN hk hr hq
  rcases prime_eq_middle_or_large_of_dvd_product_of_gt_pow_four
      hN hp hpN hk hr hq hpm with hpr | hpq
  · subst p
    rw [hphiFormula] at hphi
    rcases hrPrime.dvd_mul.mp hphi with hrq | hrrphi
    · exact hrq
    · rcases hrPrime.dvd_mul.mp hrrphi with hrr | hrphi
      · exfalso
        exact (Nat.not_dvd_of_pos_of_lt
          (by omega : 0 < r - 1) (by omega : r - 1 < r)) hrr
      · exfalso
        have hphile : Nat.totient k ≤ k := k.totient_le
        have hphilt : Nat.totient k < r := by omega
        exact (Nat.not_dvd_of_pos_of_lt
          (Nat.totient_pos.2 hkpos) hphilt) hrphi
  · subst p
    rw [hphiFormula] at hphi
    rcases hqPrime.dvd_mul.mp hphi with hqq | hqrphi
    · exfalso
      exact (Nat.not_dvd_of_pos_of_lt
        (by omega : 0 < q - 1) (by omega : q - 1 < q)) hqq
    · rcases hqPrime.dvd_mul.mp hqrphi with hqr | hqphi
      · exfalso
        have hrlekr : r ≤ k * r := by
          have hmul := Nat.mul_le_mul_right r
            (show 1 ≤ k by omega)
          simpa using hmul
        have hrltq : r - 1 < q := by omega
        exact (Nat.not_dvd_of_pos_of_lt
          (by omega : 0 < r - 1) hrltq) hqr
      · exfalso
        have hphile : Nat.totient k ≤ k := k.totient_le
        have hphilt : Nat.totient k < q := by omega
        exact (Nat.not_dvd_of_pos_of_lt
          (Nat.totient_pos.2 hkpos) hphilt) hqphi

end Erdos822
