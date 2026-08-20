/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.IsolatedDivisors
import ErdosProblems.Erdos446.BlockEstimates

/-!
# Erdős Problem 446: reciprocal mass of isolated divisors

This file sums Ford's pointwise isolated-divisor inequality over a finite
squarefree family.  It is the exact algebraic bridge from the positive
close-pair defect in the prime-block construction to the isolated-divisor
power sum used in the prescribed-multiplicity lower bound.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The isolated-divisor inequality specialized to a squarefree integer with
exactly `k` distinct prime factors. -/
theorem ford_isolated_divisor_power_lower_squarefree
    {a r k : ℕ} {sigma : ℝ} (ha : 0 < a) (hasq : Squarefree a)
    (hak : a.primeFactors.card = k) (hsigma : 0 ≤ sigma) (hr : 1 ≤ r) :
    (((2 : ℝ) ^ k) / 2) ^ (r - 1) *
        ((3 * (2 : ℝ) ^ k -
          2 * (sigmaClosePairCount a sigma : ℝ)) / 2) ≤
      (sigmaIsolatedCount a sigma : ℝ) ^ r := by
  have h := ford_isolated_divisor_power_lower a r hsigma hr
  rw [card_divisors_eq_two_pow_primeFactors_card ha hasq, hak] at h
  norm_num at h ⊢
  exact h

/-- Summed form of Ford's pointwise isolated-divisor inequality, with the
natural reciprocal weight. -/
theorem sum_ford_isolated_divisor_power_lower
    (A : Finset ℕ) (r : ℕ) {sigma : ℝ} (hsigma : 0 ≤ sigma) (hr : 1 ≤ r) :
    (∑ a ∈ A,
        (((a.divisors.card : ℝ) / 2) ^ (r - 1) *
          ((3 * (a.divisors.card : ℝ) -
            2 * (sigmaClosePairCount a sigma : ℝ)) / 2)) / (a : ℝ)) ≤
      ∑ a ∈ A, ((sigmaIsolatedCount a sigma : ℝ) ^ r) / (a : ℝ) := by
  apply Finset.sum_le_sum
  intro a ha
  exact div_le_div_of_nonneg_right
    (ford_isolated_divisor_power_lower a r hsigma hr) (Nat.cast_nonneg a)

/-- Squarefree fixed-cardinality version of the reciprocal-mass inequality. -/
theorem sum_ford_isolated_divisor_power_lower_squarefree
    (A : Finset ℕ) (r k : ℕ) {sigma : ℝ}
    (hA : ∀ a ∈ A, 0 < a ∧ Squarefree a ∧ a.primeFactors.card = k)
    (hsigma : 0 ≤ sigma) (hr : 1 ≤ r) :
    (∑ a ∈ A,
        ((((2 : ℝ) ^ k) / 2) ^ (r - 1) *
          ((3 * (2 : ℝ) ^ k -
            2 * (sigmaClosePairCount a sigma : ℝ)) / 2)) / (a : ℝ)) ≤
      ∑ a ∈ A, ((sigmaIsolatedCount a sigma : ℝ) ^ r) / (a : ℝ) := by
  apply Finset.sum_le_sum
  intro a ha
  exact div_le_div_of_nonneg_right
    (ford_isolated_divisor_power_lower_squarefree
      (hA a ha).1 (hA a ha).2.1 (hA a ha).2.2 hsigma hr)
    (Nat.cast_nonneg a)

/-- The exact implication used between Ford's positive block-mass estimate
and the isolated-divisor sum: a lower bound `B` for the reciprocal
close-pair defect yields the corresponding lower bound for the `r`th power
of the isolated-divisor count. -/
theorem isolatedPowerMass_lower_of_squarefree_defect
    (A : Finset ℕ) (r k : ℕ) {sigma B : ℝ}
    (hA : ∀ a ∈ A, 0 < a ∧ Squarefree a ∧ a.primeFactors.card = k)
    (hsigma : 0 ≤ sigma) (hr : 1 ≤ r)
    (hdefect : B ≤ ∑ a ∈ A,
      (3 * (2 : ℝ) ^ k -
        2 * (sigmaClosePairCount a sigma : ℝ)) / (a : ℝ)) :
    ((((2 : ℝ) ^ k) / 2) ^ (r - 1)) * (B / 2) ≤
      ∑ a ∈ A, ((sigmaIsolatedCount a sigma : ℝ) ^ r) / (a : ℝ) := by
  let C : ℝ := (((2 : ℝ) ^ k) / 2) ^ (r - 1)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hmul : C * (B / 2) ≤ C *
      ((∑ a ∈ A,
        (3 * (2 : ℝ) ^ k -
          2 * (sigmaClosePairCount a sigma : ℝ)) / (a : ℝ)) / 2) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hdefect (by norm_num)) hC0
  have hsum := sum_ford_isolated_divisor_power_lower_squarefree
    A r k hA hsigma hr
  have hrearrange :
      (∑ a ∈ A,
          (C * ((3 * (2 : ℝ) ^ k -
            2 * (sigmaClosePairCount a sigma : ℝ)) / 2)) / (a : ℝ)) =
        C * ((∑ a ∈ A,
          (3 * (2 : ℝ) ^ k -
            2 * (sigmaClosePairCount a sigma : ℝ)) / (a : ℝ)) / 2) := by
    calc
      (∑ a ∈ A,
          (C * ((3 * (2 : ℝ) ^ k -
            2 * (sigmaClosePairCount a sigma : ℝ)) / 2)) / (a : ℝ)) =
          ∑ a ∈ A, (C / 2) *
            ((3 * (2 : ℝ) ^ k -
              2 * (sigmaClosePairCount a sigma : ℝ)) / (a : ℝ)) := by
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = (C / 2) * (∑ a ∈ A,
            (3 * (2 : ℝ) ^ k -
              2 * (sigmaClosePairCount a sigma : ℝ)) / (a : ℝ)) := by
        rw [Finset.mul_sum]
      _ = C * ((∑ a ∈ A,
            (3 * (2 : ℝ) ^ k -
              2 * (sigmaClosePairCount a sigma : ℝ)) / (a : ℝ)) / 2) := by
        ring
  change C * (B / 2) ≤ _
  change (∑ a ∈ A,
      (C * ((3 * (2 : ℝ) ^ k -
        2 * (sigmaClosePairCount a sigma : ℝ)) / 2)) / (a : ℝ)) ≤ _ at hsum
  rw [hrearrange] at hsum
  exact hmul.trans hsum

end Erdos446
