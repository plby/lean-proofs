/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.CommonDivisorSplit

/-!
# Recovering the structured cofactor variables

The later common-divisor sums repeatedly need to pass from membership in the
image finset of odd cofactors back to its unique small, middle-prime, and
large-prime factors.  This file packages that elementary unpacking together
with the separation facts which make the two prime factors new.
-/

namespace Erdos822

open scoped BigOperators

/-- Membership in the odd raw cofactor image supplies the original
structured triple. -/
theorem exists_oddCofactorTriple_of_mem_oddRaw
    {N m : ℕ} (hm : m ∈ oddRawCofactors N) :
    ∃ k r q : ℕ,
      k ∈ oddSmallFactors N ∧
      r ∈ middlePrimes N ∧
      q ∈ largePrimes N ∧
      m = k * r * q := by
  rw [oddRawCofactors] at hm
  simp only [Finset.mem_image] at hm
  obtain ⟨⟨k, r, q⟩, ht, hmul⟩ := hm
  rw [mem_oddCofactorTriples_iff] at ht
  exact ⟨k, r, q, ht.1, ht.2.1, ht.2.2, hmul.symm⟩

/-- The structured triple supplied by odd raw membership has prime factors
which are absent from the factors preceding them. -/
theorem exists_separated_oddCofactorTriple_of_mem_oddRaw
    {N m : ℕ} (hN : 2 ≤ N) (hm : m ∈ oddRawCofactors N) :
    ∃ k r q : ℕ,
      k ∈ oddSmallFactors N ∧
      r ∈ middlePrimes N ∧
      q ∈ largePrimes N ∧
      m = k * r * q ∧
      r.Prime ∧ q.Prime ∧
      ¬ r ∣ k ∧ ¬ q ∣ k * r := by
  obtain ⟨k, r, q, hk, hr, hq, hmul⟩ :=
    exists_oddCofactorTriple_of_mem_oddRaw hm
  have ht : (k, r, q) ∈ oddCofactorTriples N := by
    rw [mem_oddCofactorTriples_iff]
    exact ⟨hk, hr, hq⟩
  have hsep := oddCofactorTriples_separated hN ht
  have hrPrime := (mem_middlePrimes_iff.mp hr).2.2
  have hqPrime := (mem_largePrimes_iff.mp hq).2.2
  refine ⟨k, r, q, hk, hr, hq, hmul, hrPrime, hqPrime, ?_, ?_⟩
  · intro hrdvd
    have hrle : r ≤ k := Nat.le_of_dvd hsep.1 hrdvd
    omega
  · intro hqdvd
    have hqle : q ≤ k * r :=
      Nat.le_of_dvd (Nat.mul_pos hsep.1 hrPrime.pos) hqdvd
    omega

/-- The same representation is available for every corrected B4 cofactor. -/
theorem exists_separated_oddCofactorTriple_of_mem_squarefreeLargeGcdFree
    {N y m : ℕ} (hN : 2 ≤ N)
    (hm : m ∈ squarefreeLargeGcdFreeOddCofactors N y) :
    ∃ k r q : ℕ,
      k ∈ oddSmallFactors N ∧
      r ∈ middlePrimes N ∧
      q ∈ largePrimes N ∧
      m = k * r * q ∧
      r.Prime ∧ q.Prime ∧
      ¬ r ∣ k ∧ ¬ q ∣ k * r := by
  exact exists_separated_oddCofactorTriple_of_mem_oddRaw hN
    (squarefreeLargeGcdFreeOddCofactors_subset_oddRaw N y hm)

/-- Generic finite Fubini expansion over the injective odd cofactor
parameterization. -/
theorem sum_oddRawCofactors_eq_triple
    {N : ℕ} (hN : 2 ≤ N) (f : ℕ → ℝ) :
    ∑ m ∈ oddRawCofactors N, f m =
      ∑ k ∈ oddSmallFactors N,
        ∑ r ∈ middlePrimes N,
          ∑ q ∈ largePrimes N, f (k * r * q) := by
  unfold oddRawCofactors
  rw [Finset.sum_image (cofactorProduct_injOn_oddCofactorTriples hN)]
  rw [oddCofactorTriples]
  change
    (∑ t ∈ oddSmallFactors N ×ˢ (middlePrimes N ×ˢ largePrimes N),
      f (cofactorProduct t)) = _
  rw [Finset.sum_product]
  simp_rw [Finset.sum_product]
  rfl

/-- A sum over any subfamily of the odd raw layer can be expanded over all
structured triples with a membership indicator. -/
theorem sum_subset_oddRawCofactors_eq_triple_if
    {N : ℕ} {B : Finset ℕ} (hN : 2 ≤ N)
    (hB : B ⊆ oddRawCofactors N) (f : ℕ → ℝ) :
    ∑ m ∈ B, f m =
      ∑ k ∈ oddSmallFactors N,
        ∑ r ∈ middlePrimes N,
          ∑ q ∈ largePrimes N,
            if k * r * q ∈ B then f (k * r * q) else 0 := by
  have hfilter :
      B = (oddRawCofactors N).filter fun m => m ∈ B := by
    ext m
    constructor
    · intro hm
      exact Finset.mem_filter.mpr ⟨hB hm, hm⟩
    · intro hm
      exact (Finset.mem_filter.mp hm).2
  calc
    (∑ m ∈ B, f m) =
        ∑ m ∈ oddRawCofactors N,
          if m ∈ B then f m else 0 := by
      rw [← Finset.sum_filter]
      rw [← hfilter]
    _ = ∑ k ∈ oddSmallFactors N,
          ∑ r ∈ middlePrimes N,
            ∑ q ∈ largePrimes N,
              if k * r * q ∈ B then f (k * r * q) else 0 :=
      sum_oddRawCofactors_eq_triple hN
        (fun m => if m ∈ B then f m else 0)

end Erdos822
