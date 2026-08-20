/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.IsolatedDivisors
import ErdosProblems.Erdos446.BlockEstimates

/-!
# Erdős Problem 446: upper bounds for elementary reciprocal masses

The upper-bound half of Ford's argument repeatedly replaces selection of
distinct primes by sampling with replacement.  This file records the exact
finite inequality

`r! * e_r(w) ≤ (∑ w)^r`

for nonnegative weights, and specializes it to the reciprocal-prime blocks.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- Sampling without replacement has no more total weight than sampling with
replacement.  The factorial accounts for all orderings of a selected set. -/
theorem factorial_mul_elementaryMass_le_pow_sum
    {α : Type*} [DecidableEq α] (P : Finset α) (w : α → ℝ)
    (hw : ∀ x ∈ P, 0 ≤ w x) (r : ℕ) :
    (r.factorial : ℝ) * elementaryMass P w r ≤
      (∑ x ∈ P, w x) ^ r := by
  induction r with
  | zero => simp [elementaryMass_zero]
  | succ r ih =>
      have hsumNonneg : 0 ≤ ∑ x ∈ P, w x :=
        Finset.sum_nonneg hw
      have hstep :
          ((r : ℝ) + 1) * elementaryMass P w (r + 1) ≤
            elementaryMass P w r * (∑ x ∈ P, w x) := by
        rw [elementaryMass_double_count]
        rw [elementaryMass, Finset.sum_mul]
        apply Finset.sum_le_sum
        intro S hS
        have hSP : S ⊆ P := (Finset.mem_powersetCard.mp hS).1
        have hweight : 0 ≤ subsetWeight w S := by
          apply Finset.prod_nonneg
          intro x hx
          exact hw x (hSP hx)
        apply mul_le_mul_of_nonneg_left _ hweight
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.sdiff_subset : P \ S ⊆ P)
          (fun x hxP _hxS ↦ hw x hxP)
      calc
        (((r + 1).factorial : ℕ) : ℝ) *
              elementaryMass P w (r + 1) =
            (r.factorial : ℝ) *
              (((r : ℝ) + 1) * elementaryMass P w (r + 1)) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        _ ≤ (r.factorial : ℝ) *
              (elementaryMass P w r * (∑ x ∈ P, w x)) := by
          gcongr
        _ = ((r.factorial : ℝ) * elementaryMass P w r) *
              (∑ x ∈ P, w x) := by ring
        _ ≤ (∑ x ∈ P, w x) ^ r * (∑ x ∈ P, w x) := by
          exact mul_le_mul_of_nonneg_right ih hsumNonneg
        _ = (∑ x ∈ P, w x) ^ (r + 1) := by
          rw [pow_succ]

theorem blockElementaryMass_upper (j r : ℕ) :
    (r.factorial : ℝ) * blockElementaryMass j r ≤
      primeBlockMass j ^ r := by
  rw [blockElementaryMass_eq_elementaryMass,
    primeBlockMass_eq_weight_sum]
  exact factorial_mul_elementaryMass_le_pow_sum
    (primeBlock j) (fun p : ℕ ↦ 1 / (p : ℝ))
    (fun p hp ↦ (primeBlock_weight_nonneg_le_endpoint_inv hp).1) r

/-- Reciprocal mass of a prescribed block-cardinality family, bounded by
the product of the independent Poisson masses of its blocks. -/
theorem blockFamily_reciprocal_sum_upper (M k : ℕ) (b : ℕ → ℕ) :
    (∑ a ∈ blockFamily M k b, 1 / (a : ℝ)) ≤
      ∏ i : Fin k,
        primeBlockMass (M + i) ^ (b i) /
          ((b i).factorial : ℝ) := by
  rw [blockFamily_reciprocal_sum_factorization]
  apply Finset.prod_le_prod
  · intro i hi
    exact elementaryMass_nonneg_of_mem
      (fun p hp ↦ (primeBlock_weight_nonneg_le_endpoint_inv hp).1) (b i)
  · intro i hi
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < (b i).factorial)).2
      (by simpa [mul_comm] using blockElementaryMass_upper (M + i) (b i))

end Erdos446
