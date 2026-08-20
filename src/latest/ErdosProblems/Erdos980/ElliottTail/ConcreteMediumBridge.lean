/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.Model
import ErdosProblems.Erdos980.ElliottTail.Definitions
import ErdosProblems.Erdos980.ElliottTail.MediumTail

/-!
# The exact prime-indexed medium-tail bridge

This file identifies the abstract prime-indexed sum used by the medium-tail
estimate with the literal sum over primes in a numerical interval of least
`k`-th-power nonresidues.  Indices are zero based.  Consequently the generic
condition `M < j` corresponds exactly to the numerical lower cutoff
`rationalPrime (M + 1) - 1`.  A second theorem records the often-used
equivalent convention in which the numerical cutoff is
`rationalPrime M - 1` and the generic index cutoff is `M - 1`.
-/

namespace Erdos980.ElliottTail

open scoped BigOperators

noncomputable section

/-- Primes below `x` whose least `k`-th-power nonresidue is the rational prime
with zero-based index `j`. -/
def primeIndexPrimes (k j x : ℕ) : Finset ℕ :=
  (primesBelow x).filter
    (fun p ↦ leastKthPowerNonresidue k p = rationalPrime j)

/-- The exact, real-valued cardinality of the `j`th least-nonresidue class
among primes strictly below `x`. -/
def primeIndexCount (k j x : ℕ) : ℝ :=
  ((primeIndexPrimes k j x).card : ℝ)

/-- The finite set of zero-based rational-prime indices whose values are at
most the numerical cutoff `Y`. -/
def primeIndicesUpTo (Y : ℕ) : Finset ℕ :=
  (Finset.range (Y + 1)).filter (fun j ↦ rationalPrime j ≤ Y)

@[simp] theorem mem_primeIndexPrimes {k j x p : ℕ} :
    p ∈ primeIndexPrimes k j x ↔
      p < x ∧ p.Prime ∧
        leastKthPowerNonresidue k p = rationalPrime j := by
  simp [primeIndexPrimes, primesBelow, and_assoc]

@[simp] theorem mem_primeIndicesUpTo {Y j : ℕ} :
    j ∈ primeIndicesUpTo Y ↔ rationalPrime j ≤ Y := by
  simp only [primeIndicesUpTo, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h ↦ h.2
  · intro h
    have hj : j + 2 ≤ rationalPrime j := by
      simpa [rationalPrime] using Nat.add_two_le_nth_prime j
    exact ⟨by omega, h⟩

/-- The strict generic index cutoff `M < j` is the numerical cutoff just
before the rational prime with index `M + 1`. -/
theorem rationalPrime_succ_sub_one_lt_iff {M j : ℕ} :
    rationalPrime (M + 1) - 1 < rationalPrime j ↔ M < j := by
  have hpos : 0 < rationalPrime (M + 1) := rationalPrime_pos (M + 1)
  constructor
  · intro h
    have hle : rationalPrime (M + 1) ≤ rationalPrime j := by omega
    have : M + 1 ≤ j :=
      rationalPrime_strictMono.le_iff_le.mp hle
    omega
  · intro h
    have hind : M + 1 ≤ j := by omega
    have hle : rationalPrime (M + 1) ≤ rationalPrime j :=
      rationalPrime_strictMono.monotone hind
    omega

/-- Multiplying an exact class count by its prime value is the sum of the
least nonresidue over that class. -/
theorem rationalPrime_mul_primeIndexCount_eq_sum
    (k j x : ℕ) :
    (rationalPrime j : ℝ) * primeIndexCount k j x =
      ∑ p ∈ primeIndexPrimes k j x,
        (leastKthPowerNonresidue k p : ℝ) := by
  unfold primeIndexCount
  calc
    (rationalPrime j : ℝ) * ((primeIndexPrimes k j x).card : ℝ) =
        ∑ _p ∈ primeIndexPrimes k j x, (rationalPrime j : ℝ) := by
      simp [nsmul_eq_mul, mul_comm]
    _ = ∑ p ∈ primeIndexPrimes k j x,
          (leastKthPowerNonresidue k p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact_mod_cast (mem_primeIndexPrimes.mp hp).2.2.symm

private theorem primeIndexPrimes_pairwiseDisjoint
    (k x : ℕ) (I : Finset ℕ) :
    (↑I : Set ℕ).PairwiseDisjoint
      (fun j ↦ primeIndexPrimes k j x) := by
  intro i _ j _ hij
  change Disjoint (primeIndexPrimes k i x) (primeIndexPrimes k j x)
  rw [Finset.disjoint_left]
  intro p hpi hpj
  have hi := (mem_primeIndexPrimes.mp hpi).2.2
  have hj := (mem_primeIndexPrimes.mp hpj).2.2
  apply hij
  exact rationalPrime_strictMono.injective (hi.symm.trans hj)

private theorem primeIndexBiUnion_eq_mediumPrimes
    {k : ℕ} (hk : 2 ≤ k) (M Y x : ℕ) :
    ((primeIndicesUpTo Y).filter (M < ·)).biUnion
        (fun j ↦ primeIndexPrimes k j x) =
      (primesBelow x).filter
        (fun p ↦ rationalPrime (M + 1) - 1 <
            leastKthPowerNonresidue k p ∧
          leastKthPowerNonresidue k p ≤ Y) := by
  classical
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨j, ⟨hjactive, hMj⟩, hpj⟩
    have hmem := mem_primeIndexPrimes.mp hpj
    have hjY := mem_primeIndicesUpTo.mp hjactive
    refine ⟨?_, ?_, ?_⟩
    · simpa [primesBelow] using ⟨hmem.1, hmem.2.1⟩
    · rw [hmem.2.2]
      exact rationalPrime_succ_sub_one_lt_iff.mpr hMj
    · simpa [hmem.2.2] using hjY
  · rintro ⟨hpx, hlower, hupper⟩
    let n := leastKthPowerNonresidue k p
    have hnpos : 0 < n := by
      dsimp [n]
      omega
    have hnzero : n ≠ 0 := hnpos.ne'
    have helig : Eligible k p := by
      have hnot := (leastKthPowerNonresidue_eq_zero_iff k p).not.mp hnzero
      exact (not_not.mp hnot).2
    have hnprime : n.Prime := leastKthPowerNonresidue_prime hk helig
    let j := Nat.count Nat.Prime n
    have hjvalue : rationalPrime j = n := by
      dsimp [j, rationalPrime]
      exact Nat.nth_count hnprime
    have hMj : M < j := by
      apply rationalPrime_succ_sub_one_lt_iff.mp
      simpa [hjvalue] using hlower
    have hjY : rationalPrime j ≤ Y := by
      simpa [hjvalue] using hupper
    refine ⟨j, ⟨mem_primeIndicesUpTo.mpr hjY, hMj⟩, ?_⟩
    apply mem_primeIndexPrimes.mpr
    have hpx' : p < x ∧ p.Prime := by
      simpa [primesBelow] using hpx
    refine ⟨?_, ?_, ?_⟩
    · exact hpx'.1
    · exact hpx'.2
    · simpa [n] using hjvalue.symm

/-- The prime-indexed medium sum is literally the normalized numerical
medium tail.  This is the exact zero-based-index convention: `M < j`
corresponds to the lower cutoff `rationalPrime (M + 1) - 1`. -/
theorem primeIndexedMediumWeightedTail_primeIndexCount_eq_normalizedMedium
    {k : ℕ} (hk : 2 ≤ k) (M Y x : ℕ) :
    primeIndexedMediumWeightedTail (primeIndexCount k)
        (fun _ ↦ primeIndicesUpTo Y) M x =
      normalizedMediumWeightedTail k
        (rationalPrime (M + 1) - 1) Y x := by
  rw [primeIndexedMediumWeightedTail_eq]
  unfold normalizedMediumWeightedTail mediumWeightedTailSum
  congr 1
  change
    (∑ j ∈ (primeIndicesUpTo Y).filter (M < ·),
      (rationalPrime j : ℝ) * primeIndexCount k j x) = _
  simp_rw [rationalPrime_mul_primeIndexCount_eq_sum]
  rw [← Finset.sum_biUnion
    (primeIndexPrimes_pairwiseDisjoint k x
      ((primeIndicesUpTo Y).filter (M < ·)))]
  rw [primeIndexBiUnion_eq_mediumPrimes hk]

/-- Equivalent convention matching the model-tail cutoff exactly: deleting
the first `M` rational-prime levels uses numerical cutoff
`rationalPrime M - 1`.  Since the generic medium sum uses a *strict* index
cutoff, its argument is `M - 1`. -/
theorem primeIndexedMediumWeightedTail_primeIndexCount_eq_normalizedMedium_sub_one
    {k : ℕ} (hk : 2 ≤ k) {M : ℕ} (hM : 0 < M) (Y x : ℕ) :
    primeIndexedMediumWeightedTail (primeIndexCount k)
        (fun _ ↦ primeIndicesUpTo Y) (M - 1) x =
      normalizedMediumWeightedTail k (rationalPrime M - 1) Y x := by
  have hindex : M - 1 + 1 = M := by omega
  simpa [hindex] using
    (primeIndexedMediumWeightedTail_primeIndexCount_eq_normalizedMedium
      hk (M - 1) Y x)

end

end Erdos980.ElliottTail
