/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.PrimeSquareRange
import ErdosProblems.Erdos822.FinsetSumUnion

/-!
# Averaging the repeated-prime-square exception

The bad cofactors are the union over candidate primes p of the p²-incidence
sets.  Finite subadditivity of nonnegative sums and the reciprocal-square
bound convert the one-prime estimate into a uniform global estimate.
-/

namespace Erdos822

open scoped BigOperators

/-- Union of all large-prime-square bad cofactor sets. -/
def largeSquareBadCoprimeOddCofactors (N y : ℕ) : Finset ℕ :=
  (largeSquarePrimes N y).biUnion fun p =>
    squareDivisibleCoprimeOddCofactors N p

@[simp]
theorem mem_largeSquareBadCoprimeOddCofactors_iff
    {N y m : ℕ} :
    m ∈ largeSquareBadCoprimeOddCofactors N y ↔
      ∃ p ∈ largeSquarePrimes N y,
        m ∈ squareDivisibleCoprimeOddCofactors N p := by
  simp [largeSquareBadCoprimeOddCofactors]

/-- Global reciprocal bound for cofactors with a repeated large prime
factor in the shifted coefficient and no common p-factor in the cofactor. -/
theorem sum_inv_largeSquareBadCoprimeOddCofactors_le
    {N y : ℕ} (hN : 2 ≤ N) (hy1 : 1 ≤ y) (hyN : y < N ^ 21) :
    ∑ m ∈ largeSquareBadCoprimeOddCofactors N y,
        (1 : ℝ) / m ≤
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          ((((1 : ℝ) / y) +
              ((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) *
            (harmonic N : ℝ)) := by
  classical
  let K : ℝ := ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k
  let R : ℝ := ∑ r ∈ middlePrimes N, (1 : ℝ) / r
  let H : ℝ := (harmonic N : ℝ)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact Finset.sum_nonneg fun k hk => by positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    exact Finset.sum_nonneg fun r hr => by positivity
  have hH : 0 ≤ H := by
    dsimp [H]
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity
  have hsub :
      (∑ m ∈ largeSquareBadCoprimeOddCofactors N y,
          (1 : ℝ) / m) ≤
        ∑ p ∈ largeSquarePrimes N y,
          ∑ m ∈ squareDivisibleCoprimeOddCofactors N p,
            (1 : ℝ) / m := by
    unfold largeSquareBadCoprimeOddCofactors
    apply sum_biUnion_le_sum
    intro p hp m hm
    positivity
  have hpoint : ∀ p ∈ largeSquarePrimes N y,
      ∑ m ∈ squareDivisibleCoprimeOddCofactors N p,
          (1 : ℝ) / m ≤
        K * R *
          (((1 : ℝ) / (p ^ 2 : ℕ) +
              (1 : ℝ) / (N ^ 21 : ℕ)) * H) := by
    intro p hpMem
    have hp := (mem_largeSquarePrimes_iff.mp hpMem).2.2
    simpa [K, R, H] using
      (sum_inv_squareDivisibleCoprimeOddCofactors_le hN hp hyN)
  calc
    (∑ m ∈ largeSquareBadCoprimeOddCofactors N y,
        (1 : ℝ) / m) ≤
        ∑ p ∈ largeSquarePrimes N y,
          ∑ m ∈ squareDivisibleCoprimeOddCofactors N p,
            (1 : ℝ) / m := hsub
    _ ≤ ∑ p ∈ largeSquarePrimes N y,
          K * R *
            (((1 : ℝ) / (p ^ 2 : ℕ) +
                (1 : ℝ) / (N ^ 21 : ℕ)) * H) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hpoint p hp
    _ = K * R *
          (((∑ p ∈ largeSquarePrimes N y,
              (1 : ℝ) / (p ^ 2 : ℕ)) +
              ((largeSquarePrimes N y).card : ℝ) /
                (N ^ 21 : ℕ)) * H) := by
      rw [← Finset.mul_sum, ← Finset.sum_mul,
        Finset.sum_add_distrib]
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul]
      push_cast
      ring
    _ ≤ K * R *
          ((((1 : ℝ) / y) +
              ((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) * H) := by
      have hsquares :
          ∑ p ∈ largeSquarePrimes N y,
              (1 : ℝ) / (p ^ 2 : ℕ) ≤
            (1 : ℝ) / y :=
        sum_inv_sq_largeSquarePrimes_le_inv hy1
      have hcard :
          ((largeSquarePrimes N y).card : ℝ) ≤
            ((2 * N ^ 14 : ℕ) : ℝ) := by
        exact_mod_cast largeSquarePrimes_card_le N y
      have hden : 0 ≤ ((N ^ 21 : ℕ) : ℝ) := by positivity
      have hinside :
          (∑ p ∈ largeSquarePrimes N y,
              (1 : ℝ) / (p ^ 2 : ℕ)) +
              ((largeSquarePrimes N y).card : ℝ) /
                (N ^ 21 : ℕ) ≤
            (1 : ℝ) / y +
              ((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ) := by
        exact add_le_add hsquares
          (div_le_div_of_nonneg_right hcard hden)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hinside hH)
        (mul_nonneg hK hR)
    _ = (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          ((((1 : ℝ) / y) +
              ((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) *
            (harmonic N : ℝ)) := by
      rfl

end Erdos822
