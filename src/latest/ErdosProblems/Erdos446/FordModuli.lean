/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.EulerEstimate
import ErdosProblems.Erdos446.SieveFamilyLower

/-!
# Erdős Problem 446: Ford's squarefree `a*p` moduli

For a small squarefree integer `a`, retain primes `p` for which some divisor
`d ∣ a` makes `d*p` lie in the target interval.  The exact support of `a*p`
then gives a disjoint CRT cell contained in the divisor event.
-/

namespace Erdos446

open Finset Set Real
open scoped BigOperators

/-- Primes `p ≤ 2y` for which `a` has a divisor `d` with `y < d*p ≤ 2y`. -/
def eligiblePrimes (y a : ℕ) : Finset ℕ :=
  (Nat.primesLE (2 * y)).filter fun p ↦
    ∃ d ∈ a.divisors, y < d * p ∧ d * p ≤ 2 * y

/-- The reciprocal mass of the eligible primes. -/
noncomputable def eligiblePrimeMass (y a : ℕ) : ℝ :=
  ∑ p ∈ eligiblePrimes y a, 1 / (p : ℝ)

/-- Pairs in Ford's lower construction. -/
def fordPairs (y : ℕ) (A : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ Nat.primesLE (2 * y)).filter fun ap ↦
    ∃ d ∈ ap.1.divisors, y < d * ap.2 ∧ d * ap.2 ≤ 2 * y

/-- The exact-support moduli `a*p`. -/
def fordModuli (y : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (fordPairs y A).image fun ap ↦ ap.1 * ap.2

theorem mem_eligiblePrimes {y a p : ℕ} :
    p ∈ eligiblePrimes y a ↔
      p.Prime ∧ p ≤ 2 * y ∧
        ∃ d ∈ a.divisors, y < d * p ∧ d * p ≤ 2 * y := by
  simp [eligiblePrimes, Nat.mem_primesLE, and_comm, and_left_comm, and_assoc]

theorem mem_fordPairs {y : ℕ} {A : Finset ℕ} {a p : ℕ} :
    (a, p) ∈ fordPairs y A ↔
      a ∈ A ∧ p.Prime ∧ p ≤ 2 * y ∧
        ∃ d ∈ a.divisors, y < d * p ∧ d * p ≤ 2 * y := by
  simp [fordPairs, Nat.mem_primesLE, and_comm, and_left_comm, and_assoc]

private theorem eligible_prime_gt_bound
    {y B a p : ℕ} (haB : a ≤ B) (hBsq : B * B < y)
    (hp : p ∈ eligiblePrimes y a) :
    B < p := by
  obtain ⟨hpPrime, hpY, d, hd, hydp, hdp⟩ := mem_eligiblePrimes.mp hp
  have hda : d ≤ a := Nat.divisor_le hd
  by_contra hpB
  have hmul : d * p ≤ B * B := Nat.mul_le_mul (hda.trans haB) (le_of_not_gt hpB)
  omega

/-- The product map is injective on the selected pairs: the large prime is
larger than every possible small factor. -/
theorem fordPair_product_injOn
    {y B : ℕ} {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 0 < a) (hbound : ∀ a ∈ A, a ≤ B)
    (hBsq : B * B < y) :
    Set.InjOn (fun ap : ℕ × ℕ ↦ ap.1 * ap.2) (fordPairs y A) := by
  rintro ⟨a, p⟩ hap ⟨b, q⟩ hbq heq
  change a * p = b * q at heq
  have hmemAP := mem_fordPairs.mp hap
  have hmemBQ := mem_fordPairs.mp hbq
  have hpElig : p ∈ eligiblePrimes y a := mem_eligiblePrimes.mpr
    ⟨hmemAP.2.1, hmemAP.2.2.1, hmemAP.2.2.2⟩
  have hqElig : q ∈ eligiblePrimes y b := mem_eligiblePrimes.mpr
    ⟨hmemBQ.2.1, hmemBQ.2.2.1, hmemBQ.2.2.2⟩
  have hpB : B < p := eligible_prime_gt_bound
    (hbound a hmemAP.1) hBsq hpElig
  have hqB : B < q := eligible_prime_gt_bound
    (hbound b hmemBQ.1) hBsq hqElig
  have hpDiv : p ∣ b * q := by
    rw [← heq]
    exact dvd_mul_left p a
  have hpNotB : ¬p ∣ b := by
    intro hpb
    have hpLeB : p ≤ b := Nat.le_of_dvd (hpos b hmemBQ.1) hpb
    exact (not_le_of_gt hpB) (hpLeB.trans (hbound b hmemBQ.1))
  have hpq : p ∣ q := ((hmemAP.2.1.dvd_mul).mp hpDiv).resolve_left hpNotB
  have hpEqQ : p = q := by
    rcases (Nat.dvd_prime hmemBQ.2.1).mp hpq with hp1 | hpqEq
    · exact (hmemAP.2.1.ne_one hp1).elim
    · exact hpqEq
  subst q
  have hab : a = b := Nat.mul_right_cancel hmemAP.2.1.pos heq
  subst b
  rfl

theorem fordModuli_reciprocal_sum
    {y B : ℕ} {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 0 < a) (hbound : ∀ a ∈ A, a ≤ B)
    (hBsq : B * B < y) :
    (∑ c ∈ fordModuli y A, 1 / (c : ℝ)) =
      ∑ a ∈ A, (1 / (a : ℝ)) * eligiblePrimeMass y a := by
  rw [fordModuli, Finset.sum_image (fordPair_product_injOn hpos hbound hBsq)]
  rw [fordPairs, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  rw [eligiblePrimeMass, eligiblePrimes, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hgood : ∃ d ∈ a.divisors, y < d * p ∧ d * p ≤ 2 * y
  · simp only [hgood, if_true]
    push_cast
    ring
  · simp only [hgood, if_false, mul_zero]

theorem fordModuli_squarefree
    {y B : ℕ} {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 0 < a) (hbound : ∀ a ∈ A, a ≤ B)
    (hBsq : B * B < y) (hsq : ∀ a ∈ A, Squarefree a) :
    ∀ c ∈ fordModuli y A, Squarefree c := by
  intro c hc
  rcases Finset.mem_image.mp hc with ⟨⟨a, p⟩, hap, rfl⟩
  have hmem := mem_fordPairs.mp hap
  have hpElig : p ∈ eligiblePrimes y a := mem_eligiblePrimes.mpr
    ⟨hmem.2.1, hmem.2.2.1, hmem.2.2.2⟩
  have hpB : B < p := eligible_prime_gt_bound
    (hbound a hmem.1) hBsq hpElig
  have hpNotDvd : ¬p ∣ a := by
    intro hpa
    have : p ≤ a := Nat.le_of_dvd (hpos a hmem.1) hpa
    exact (not_le_of_gt hpB) (this.trans (hbound a hmem.1))
  have hcop : a.Coprime p := by
    rw [Nat.coprime_comm]
    exact hmem.2.1.coprime_iff_not_dvd.mpr hpNotDvd
  exact (Nat.squarefree_mul hcop).mpr ⟨hsq a hmem.1, hmem.2.1.squarefree⟩

theorem fordModuli_primeFactorsAtMost
    {y B : ℕ} {A : Finset ℕ} (hBy : B ≤ 2 * y)
    (hbound : ∀ a ∈ A, a ≤ B) :
    ∀ c ∈ fordModuli y A, PrimeFactorsAtMost (2 * y) c := by
  intro c hc r hr
  rcases Finset.mem_image.mp hc with ⟨⟨a, p⟩, hap, rfl⟩
  have hmem := mem_fordPairs.mp hap
  obtain ⟨d, hd, hydp, hdp⟩ := hmem.2.2.2
  rw [Nat.primeFactors_mul (Nat.mem_divisors.mp hd).2 hmem.2.1.ne_zero] at hr
  rcases Finset.mem_union.mp hr with hra | hrp
  · exact (Nat.le_of_mem_primeFactors hra).trans ((hbound a hmem.1).trans hBy)
  · have : r = p := by
      simpa [Nat.Prime.primeFactors hmem.2.1] using hrp
    subst r
    exact hmem.2.2.1

theorem fordModuli_interval_witness
    {y : ℕ} {A : Finset ℕ} :
    ∀ c ∈ fordModuli y A, ∃ d ∈ Finset.Ioc y (2 * y), d ∣ c := by
  intro c hc
  rcases Finset.mem_image.mp hc with ⟨⟨a, p⟩, hap, rfl⟩
  have hmem := mem_fordPairs.mp hap
  obtain ⟨d, hd, hydp, hdp⟩ := hmem.2.2.2
  exact ⟨d * p, Finset.mem_Ioc.mpr ⟨hydp, hdp⟩,
    Nat.mul_dvd_mul_right (Nat.dvd_of_mem_divisors hd) p⟩

/-- Ford's exact-support lower reduction, prior to estimating the prime mass
by logarithmic cluster length. -/
theorem ford_moduli_lower
    {y B : ℕ} {A : Finset ℕ} (hy : 0 < y) (hBy : B ≤ 2 * y)
    (hpos : ∀ a ∈ A, 0 < a) (hbound : ∀ a ∈ A, a ≤ B)
    (hBsq : B * B < y) (hsq : ∀ a ∈ A, Squarefree a) :
    smallPrimeEulerDensity (2 * y) *
        (∑ a ∈ A, (1 / (a : ℝ)) * eligiblePrimeMass y a) ≤
      epsilon y (2 * y) := by
  rw [← fordModuli_reciprocal_sum hpos hbound hBsq]
  exact squarefree_moduli_lower_bound hy
    (fordModuli_squarefree hpos hbound hBsq hsq)
    (fordModuli_primeFactorsAtMost hBy hbound)
    fordModuli_interval_witness

end Erdos446
