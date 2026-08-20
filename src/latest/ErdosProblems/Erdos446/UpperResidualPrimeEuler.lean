/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperTrimmedPrimeBlocks

/-!
# Erdős Problem 446: the residual-prime Euler factor

The one-sided block trimming leaves a geometrically summable family of
residual primes.  This file packages the residuals from any finite run of
consecutive Ford blocks and proves that arbitrary squarefree choices from
that pool cost a single Euler factor, uniformly in the number of blocks.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable section

/-- The residual primes in the consecutive blocks `M, ..., M + K - 1`. -/
def residualPrimePool (M K : ℕ) : Finset ℕ :=
  (Finset.range K).biUnion (fun i ↦ residualPrimeBlock (M + i))

theorem residualPrimeBlock_pairwise_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (residualPrimeBlock i) (residualPrimeBlock j) :=
  Disjoint.mono (residualPrimeBlock_subset i) (residualPrimeBlock_subset j)
    (primeBlock_pairwise_disjoint hij)

theorem residualPrimeBlock_shift_pairwiseDisjoint (M K : ℕ) :
    (↑(Finset.range K) : Set ℕ).PairwiseDisjoint
      (fun i ↦ residualPrimeBlock (M + i)) := by
  intro i hi j hj hij
  apply residualPrimeBlock_pairwise_disjoint
  omega

theorem sum_residualPrimePool (M K : ℕ) :
    (∑ p ∈ residualPrimePool M K, 1 / (p : ℝ)) =
      ∑ i ∈ Finset.range K, residualPrimeBlockMass (M + i) := by
  rw [residualPrimePool, Finset.sum_biUnion
    (residualPrimeBlock_shift_pairwiseDisjoint M K)]
  rfl

/-- The geometric tail beginning at block `M`, truncated after `K` terms. -/
theorem shifted_geometric_half_sum_le (M K : ℕ) :
    (∑ i ∈ Finset.range K, 1 / (2 : ℝ) ^ (M + i)) ≤
      2 / (2 : ℝ) ^ M := by
  have hgeom := sum_geometric_two_le K
  calc
    (∑ i ∈ Finset.range K, 1 / (2 : ℝ) ^ (M + i)) =
        (1 / (2 : ℝ) ^ M) *
          ∑ i ∈ Finset.range K, (1 / 2 : ℝ) ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [pow_add, one_div, mul_inv_rev, inv_pow]
      ring
    _ ≤ (1 / (2 : ℝ) ^ M) * 2 := by
      exact mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 2 / (2 : ℝ) ^ M := by ring

/-- A geometric blockwise residual estimate sums to one absolute tail
bound, independently of the number `K` of blocks retained. -/
theorem residualPrimePool_reciprocalMass_le
    {C : ℝ} (hC : 0 ≤ C) {J M K : ℕ} (hJM : J ≤ M)
    (hmass : ∀ j : ℕ, J ≤ j →
      |primeBlockMass j - Real.log 2| ≤ C / (2 : ℝ) ^ j) :
    (∑ p ∈ residualPrimePool M K, 1 / (p : ℝ)) ≤
      2 * (C + 1) / (2 : ℝ) ^ M := by
  rw [sum_residualPrimePool]
  calc
    (∑ i ∈ Finset.range K, residualPrimeBlockMass (M + i)) ≤
        ∑ i ∈ Finset.range K, (C + 1) / (2 : ℝ) ^ (M + i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact residualPrimeBlockMass_le hC (hmass (M + i) (by omega))
    _ = (C + 1) *
        ∑ i ∈ Finset.range K, 1 / (2 : ℝ) ^ (M + i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (C + 1) * (2 / (2 : ℝ) ^ M) := by
      exact mul_le_mul_of_nonneg_left (shifted_geometric_half_sum_le M K)
        (by linarith)
    _ = 2 * (C + 1) / (2 : ℝ) ^ M := by ring

/-- Every finite subset of the residual pool has no more reciprocal mass
than the full pool. -/
theorem residualSupport_reciprocalMass_le
    {C : ℝ} (hC : 0 ≤ C) {J M K : ℕ} (hJM : J ≤ M)
    (hmass : ∀ j : ℕ, J ≤ j →
      |primeBlockMass j - Real.log 2| ≤ C / (2 : ℝ) ^ j)
    {S : Finset ℕ} (hS : S ⊆ residualPrimePool M K) :
    (∑ p ∈ S, 1 / (p : ℝ)) ≤
      2 * (C + 1) / (2 : ℝ) ^ M := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg hS
    (fun p hpPool hpNot ↦ by positivity)).trans
      (residualPrimePool_reciprocalMass_le hC hJM hmass)

/-- The Euler factor for an arbitrary finite residual support is uniformly
bounded by the exponential of the total geometric residual mass. -/
theorem residualSupport_eulerProduct_le
    {C : ℝ} (hC : 0 ≤ C) {J M K : ℕ} (hJM : J ≤ M)
    (hmass : ∀ j : ℕ, J ≤ j →
      |primeBlockMass j - Real.log 2| ≤ C / (2 : ℝ) ^ j)
    {S : Finset ℕ} (hS : S ⊆ residualPrimePool M K) :
    (∏ p ∈ S, (1 + 2 / (p : ℝ))) ≤
      Real.exp (4 * (C + 1) / (2 : ℝ) ^ M) := by
  have hprod := Real.prod_one_add_le_exp_sum S
    (f := fun p ↦ 2 / (p : ℝ)) (fun p ↦ by positivity)
  calc
    (∏ p ∈ S, (1 + 2 / (p : ℝ))) ≤
        Real.exp (∑ p ∈ S, 2 / (p : ℝ)) := by
      simpa only using hprod
    _ = Real.exp (2 * ∑ p ∈ S, 1 / (p : ℝ)) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ Real.exp (4 * (C + 1) / (2 : ℝ) ^ M) := by
      apply Real.exp_le_exp.mpr
      have hs := residualSupport_reciprocalMass_le hC hJM hmass hS
      calc
        2 * ∑ p ∈ S, 1 / (p : ℝ) ≤
            2 * (2 * (C + 1) / (2 : ℝ) ^ M) :=
          mul_le_mul_of_nonneg_left hs (by norm_num)
        _ = 4 * (C + 1) / (2 : ℝ) ^ M := by ring

/-- Powerset expansion of the preceding Euler factor.  The term indexed by
`T` is exactly the weight attached to choosing the squarefree residual
support `T`. -/
theorem sum_squarefreeResidualSupports_le
    {C : ℝ} (hC : 0 ≤ C) {J M K : ℕ} (hJM : J ≤ M)
    (hmass : ∀ j : ℕ, J ≤ j →
      |primeBlockMass j - Real.log 2| ≤ C / (2 : ℝ) ^ j)
    {S : Finset ℕ} (hS : S ⊆ residualPrimePool M K) :
    (∑ T ∈ S.powerset, ∏ p ∈ T, 2 / (p : ℝ)) ≤
      Real.exp (4 * (C + 1) / (2 : ℝ) ^ M) := by
  rw [← Finset.prod_one_add]
  exact residualSupport_eulerProduct_le hC hJM hmass hS

/-- Fully instantiated form using the proved quantitative Mertens theorem.
The constants `C,J` are absolute and work simultaneously for every finite
run of blocks and every residual support drawn from it. -/
theorem exists_residualSupport_eulerProduct_le :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, ∀ M : ℕ, J ≤ M → ∀ K : ℕ,
      ∀ S : Finset ℕ, S ⊆ residualPrimePool M K →
        (∏ p ∈ S, (1 + 2 / (p : ℝ))) ≤
          Real.exp (4 * (C + 1) / (2 : ℝ) ^ M) := by
  obtain ⟨C, hC, J, hmass⟩ :=
    exists_primeBlockMass_geometric_error_threshold
  refine ⟨C, hC, J, ?_⟩
  intro M hJM K S hS
  exact residualSupport_eulerProduct_le hC.le hJM hmass hS

end

end Erdos446
