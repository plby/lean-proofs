/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperExceptionalKthLayer
import ErdosProblems.Erdos446.UpperLayerPartitionSum

/-!
# Erdős Problem 446: summing the exceptional bounds over all layers

This is the exact finite assembly corresponding to the first line of
Ford's (33a).  A reciprocal-factorial majorant `R m` for the discrete
`T(k,v,m)` set is transferred to the actual prime-block cluster mass and
summed over the canonical `k+1` integral layers.  The factor `2^(k+1)` is
pulled out exactly, leaving the dyadic weight `R m / 2^m` needed by the
double-exponential numerical estimate.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Sum arbitrary sharp reciprocal-factorial bounds for the discrete Ford
sets over every canonical layer. -/
theorem blockClusterMassOver_compositions_le_fordWeightedMassSum
    {M k v : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hM : k + blockLayerSlack k + 1 ≤ 2 ^ M)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (R : ℕ → ℝ)
    (hford : ∀ m : ℕ, m ≤ k →
      reciprocalFactorialMassOver (fordWeightedOccupancies k v m) ≤ R m) :
    blockClusterMassOver M (compositionsOf v k) ≤
      sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) *
        Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) *
          (∑ m ∈ Finset.range (k + 1), R m / (2 : ℝ) ^ m) := by
  rw [← sum_blockIntegerDyadicLayer_clusterMass M k v]
  calc
    (∑ m ∈ Finset.range (k + 1),
        blockClusterMassOver M (blockIntegerDyadicLayer k v m)) ≤
        ∑ m ∈ Finset.range (k + 1),
          (sharpBlockLayerScale M * (2 : ℝ) ^ (k - m + 1)) *
            Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) * R m := by
      apply Finset.sum_le_sum
      intro m hm
      have hmk : m ≤ k := by
        have hmlt := Finset.mem_range.mp hm
        omega
      exact blockIntegerDyadicLayer_mass_le_of_fordWeightedMass_uniform
        hC hmk hM hmass (hford m hmk)
    _ = sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) *
        Real.log 2 ^ k * Real.exp (4 * C / Real.log 2) *
          (∑ m ∈ Finset.range (k + 1), R m / (2 : ℝ) ^ m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hmk : m ≤ k := by
        have hmlt := Finset.mem_range.mp hm
        omega
      have hp : (2 : ℝ) ^ (k - m + 1) =
          (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m := by
        apply (eq_div_iff (by positivity : (2 : ℝ) ^ m ≠ 0)).2
        rw [← pow_add]
        congr 1
        omega
      rw [hp]
      ring

end Erdos446
