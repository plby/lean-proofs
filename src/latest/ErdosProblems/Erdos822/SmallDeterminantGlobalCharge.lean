/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SmallDeterminantFilteredAverage

/-!
# Global admissible determinant charge at a fixed anchor and divisor

This module sums the checked fixed-`(k,r)` determinant-prime estimate over
the unique structured representation `m=k*r*q`.  It is the Fubini step
needed by the small common-divisor range.
-/

namespace Erdos822

open scoped BigOperators

/-- Sum of the admissible determinant-prime charge over all small factors
and middle primes, with the cofactor reciprocal weight restored. -/
noncomputable def fixedAnchorDivisorDeterminantCharge
    (B : Finset ℕ) (N x m' h U z : ℕ) : ℝ :=
  ∑ k ∈ oddSmallFactors N,
    ∑ r ∈ middlePrimes N,
      ((1 : ℝ) / (k * r)) *
        ∑ p ∈ smallDeterminantPrimes U z k r h,
          ((1 : ℝ) / p) *
            ∑ q ∈ smallDeterminantLargePrimeFiberIn B N x k r m' p h,
              (1 : ℝ) / q

/-- The global fixed-anchor charge inherits the inverse-`h` and
reciprocal-square cutoff saving. -/
theorem fixedAnchorDivisorDeterminantCharge_le
    {B : Finset ℕ} {N x m' h U z cutoff y : ℕ}
    (hN : 2 ≤ N) (hm' : 0 < m')
    (hlarge : ∀ k ∈ oddSmallFactors N, ∀ r ∈ middlePrimes N,
      ∀ q ∈ largePrimes N,
        ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s)
    (hlarge' : ∀ s ∈ outerPrimes x m', m' < s)
    (hB : B ⊆ largeGcdFreeOddCofactors N cutoff)
    (hsupport : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ h → cutoff < ℓ)
    (hh : 0 < h) (hz : 1 ≤ z) (hy : y < N ^ 21) :
    fixedAnchorDivisorDeterminantCharge B N x m' h U z ≤
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          ((harmonic N : ℝ) *
            (((1 : ℝ) / h) * ((1 : ℝ) / z) +
              ((1 : ℝ) / (N ^ 21 : ℕ)) * ((U : ℝ) / z))) := by
  classical
  let C : ℝ := (harmonic N : ℝ) *
    (((1 : ℝ) / h) * ((1 : ℝ) / z) +
      ((1 : ℝ) / (N ^ 21 : ℕ)) * ((U : ℝ) / z))
  have hpoint : ∀ k ∈ oddSmallFactors N, ∀ r ∈ middlePrimes N,
      (∑ p ∈ smallDeterminantPrimes U z k r h,
          ((1 : ℝ) / p) *
            (∑ q ∈ smallDeterminantLargePrimeFiberIn B N x k r m' p h,
              (1 : ℝ) / q)) ≤ C := by
    intro k hk r hr
    exact sum_weighted_smallDeterminantLargePrimeFiberIn_le_cutoff
      hN hk hr hm' (hlarge k hk r hr) hlarge' hB hsupport hh hz hy
  unfold fixedAnchorDivisorDeterminantCharge
  calc
    (∑ k ∈ oddSmallFactors N,
      ∑ r ∈ middlePrimes N,
        ((1 : ℝ) / (k * r)) *
          ∑ p ∈ smallDeterminantPrimes U z k r h,
            ((1 : ℝ) / p) *
              ∑ q ∈ smallDeterminantLargePrimeFiberIn B N x k r m' p h,
                (1 : ℝ) / q) ≤
        ∑ k ∈ oddSmallFactors N,
          ∑ r ∈ middlePrimes N,
            ((1 : ℝ) / (k * r)) * C := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hpoint k hk r hr) (by positivity)
    _ = (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * C := by
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      have hk0 : (k : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (oddSmallFactors_pos hk))
      have hrPrime := (mem_middlePrimes_iff.mp hr).2.2
      have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hrPrime.ne_zero
      push_cast
      field_simp
    _ = (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          ((harmonic N : ℝ) *
            (((1 : ℝ) / h) * ((1 : ℝ) / z) +
              ((1 : ℝ) / (N ^ 21 : ℕ)) * ((U : ℝ) / z))) := by
      rfl

end Erdos822
