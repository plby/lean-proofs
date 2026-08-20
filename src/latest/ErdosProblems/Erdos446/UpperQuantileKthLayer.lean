/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.WeightedQuantileBridge
import ErdosProblems.Erdos446.UpperBlockMassError
import ErdosProblems.Erdos446.SmirnovQuantitative

/-!
# Erdős Problem 446: fixed-window weighted sharp layers

The quantile comparison is applied here to the actual prime-block weights.
Unlike the earlier pointwise error bridge, these estimates have no condition
relating the Smirnov offset to `2^M`.  Thus `M` may be fixed while `k` and `v`
grow.  The one-cell displacement of the barrier is the only price paid for
the nonuniform categorical law.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- A sharp layer is controlled by the shifted uniform Smirnov probability
after normalizing by the actual mass of the whole prime-block window. -/
theorem sharpBlockDyadicLayer_clusterMass_le_quantile
    {M k v m : ℕ} {C : ℝ} (hv : 0 < v)
    (hk : k < m + blockLayerSlack k + v)
    (hC : 0 ≤ C)
    (hmass : ∀ i : ℕ,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i))
    (hsmall : 4 * C ≤ Real.log 2 * (2 : ℝ) ^ M) :
    blockClusterMassOver M (sharpBlockDyadicLayer M k v m) ≤
      (sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m) *
        (primeBlockWindowMass M v ^ k *
          smirnovProbability k (m + blockLayerSlack k + 1) v /
            (k.factorial : ℝ)) := by
  let A := sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg
      (mul_nonneg (sharpBlockLayerScale_pos M).le (by positivity))
      (by positivity)
  have hcluster := blockClusterMassOver_le_weightedOccupancyMass
    (M := M) (I := sharpBlockDyadicLayer M k v m) hA
      (fun b hb a ha ↦ sharpBlockDyadicLayer_clusterLength_le hb ha)
  have hsubset : sharpBlockDyadicLayer M k v m ⊆
      smirnovOccupancies k (m + blockLayerSlack k) v :=
    sharpBlockDyadicLayer_subset_smirnov M k v m
  have hcompNonneg : ∀ b : Fin v → ℕ,
      0 ≤ weightedCompositionMass (primeBlockCellMass M v) b := by
    intro b
    dsimp [weightedCompositionMass, primeBlockCellMass]
    exact div_nonneg
      (Finset.prod_nonneg fun i hi ↦
        pow_nonneg (primeBlockMass_nonneg _) _)
      (by dsimp [compositionFactorial]; positivity)
  have hmono :
      weightedOccupancyMassOver (primeBlockCellMass M v)
          (sharpBlockDyadicLayer M k v m) ≤
        weightedOccupancyMassOver (primeBlockCellMass M v)
          (smirnovOccupancies k (m + blockLayerSlack k) v) := by
    rw [weightedOccupancyMassOver, weightedOccupancyMassOver]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun b hb hnot ↦ hcompNonneg b)
  have hquant := weightedOccupancyMassOver_smirnov_le_quantile_of_error
    (M := M) (k := k) (u := m + blockLayerSlack k) hv hk hC hmass hsmall
  calc
    blockClusterMassOver M (sharpBlockDyadicLayer M k v m) ≤
        A * weightedOccupancyMassOver (primeBlockCellMass M v)
          (sharpBlockDyadicLayer M k v m) := hcluster
    _ ≤ A * weightedOccupancyMassOver (primeBlockCellMass M v)
          (smirnovOccupancies k (m + blockLayerSlack k) v) :=
      mul_le_mul_of_nonneg_left hmono hA
    _ ≤ A * (primeBlockWindowMass M v ^ k *
          smirnovProbability k (m + blockLayerSlack k + 1) v /
            (k.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hquant hA

/-- The same fixed-window layer comparison with the actual window mass
replaced by the exact base `v * log 2` and one global geometric-error factor.
The error does not grow with the barrier offset. -/
theorem sharpBlockDyadicLayer_clusterMass_le_quantile_logBase
    {M k v m : ℕ} {C : ℝ} (hv : 0 < v)
    (hk : k < m + blockLayerSlack k + v)
    (hkv : k ≤ 10 * v) (hC : 0 ≤ C)
    (hmass : ∀ i : ℕ,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i))
    (hsmall : 4 * C ≤ Real.log 2 * (2 : ℝ) ^ M) :
    blockClusterMassOver M (sharpBlockDyadicLayer M k v m) ≤
      (sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m) *
        ((((v : ℝ) * Real.log 2) ^ k *
            Real.exp (40 * C / (Real.log 2 * (2 : ℝ) ^ M))) *
          smirnovProbability k (m + blockLayerSlack k + 1) v /
            (k.factorial : ℝ)) := by
  have hraw := sharpBlockDyadicLayer_clusterMass_le_quantile
    (M := M) (k := k) (v := v) (m := m) hv hk hC hmass hsmall
  have hmassFin : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val) := by
    intro i
    exact hmass i.val
  have hwindowPow : primeBlockWindowMass M v ^ k ≤
      ((v : ℝ) * Real.log 2) ^ k *
        Real.exp (40 * C / (Real.log 2 * (2 : ℝ) ^ M)) := by
    rw [primeBlockWindowMass, primeBlockPrefixMass,
      ← Fin.sum_univ_eq_sum_range]
    exact primeBlockMass_sum_pow_upper hC hv hkv hmassFin
  have hprobNonneg : 0 ≤
      smirnovProbability k (m + blockLayerSlack k + 1) v :=
    smirnovProbability_nonneg _ _ _
  apply hraw.trans
  apply mul_le_mul_of_nonneg_left _ (by
    exact div_nonneg
      (mul_nonneg (sharpBlockLayerScale_pos M).le (by positivity))
      (by positivity))
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hwindowPow hprobNonneg) (by positivity)

/-- Quantitative central-range form.  The one-cell quantile displacement
changes `(u,w)` to `(u+1,w+1)`.  The harmless factor two converts the
quantitative `1/k` denominator into the exact `(k+1)!` normalization. -/
theorem sharpBlockDyadicLayer_clusterMass_le_quantile_twentyfour
    {M k v m w : ℕ} {C : ℝ} (hv : 0 < v)
    (hk : 100 ≤ k)
    (hu : 10 * (m + blockLayerSlack k + 1) ≤ k)
    (hwSq : (w + 1) * (w + 1) ≤ k)
    (hw : 0 < w)
    (hrel : m + blockLayerSlack k + v = k + w)
    (hkv : k ≤ 10 * v) (hC : 0 ≤ C)
    (hmass : ∀ i : ℕ,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i))
    (hsmall : 4 * C ≤ Real.log 2 * (2 : ℝ) ^ M) :
    blockClusterMassOver M (sharpBlockDyadicLayer M k v m) ≤
      (sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m) *
        (((v : ℝ) * Real.log 2) ^ k *
          Real.exp (40 * C / (Real.log 2 * (2 : ℝ) ^ M)) *
          (48 * ((m : ℝ) + (blockLayerSlack k : ℝ) + 2) *
            ((w : ℝ) + 2) ^ 2) /
          ((k + 1).factorial : ℝ)) := by
  have hkBarrier : k < m + blockLayerSlack k + v := by omega
  have hrelShift :
      (m + blockLayerSlack k + 1) + v = k + (w + 1) := by omega
  have hprob := smirnovProbability_le_twentyfour
    (k := k) (u := m + blockLayerSlack k + 1) (v := v) (w := w + 1)
    hk hu hwSq (by omega) hrelShift
  have hraw := sharpBlockDyadicLayer_clusterMass_le_quantile_logBase
    (M := M) (k := k) (v := v) (m := m) hv hkBarrier hkv hC hmass hsmall
  apply hraw.trans
  have hkPosR : (0 : ℝ) < k := by positivity
  have hfactPos : (0 : ℝ) < k.factorial := by positivity
  have hkTwo : (k + 1 : ℝ) ≤ 2 * k := by
    exact_mod_cast (show k + 1 ≤ 2 * k by omega)
  have hprob' :
      smirnovProbability k (m + blockLayerSlack k + 1) v ≤
        48 * ((m : ℝ) + (blockLayerSlack k : ℝ) + 2) *
          ((w : ℝ) + 2) ^ 2 / ((k : ℝ) + 1) := by
    calc
      smirnovProbability k (m + blockLayerSlack k + 1) v ≤
          24 * ((m : ℝ) + (blockLayerSlack k : ℝ) + 2) *
            ((w : ℝ) + 2) ^ 2 / (k : ℝ) := by
        convert hprob using 1
        all_goals norm_num [Nat.cast_add]
        all_goals ring
      _ ≤ 48 * ((m : ℝ) + (blockLayerSlack k : ℝ) + 2) *
            ((w : ℝ) + 2) ^ 2 / ((k : ℝ) + 1) := by
        have hnum : (0 : ℝ) ≤
            24 * ((m : ℝ) + (blockLayerSlack k : ℝ) + 2) *
              ((w : ℝ) + 2) ^ 2 := by positivity
        rw [div_le_div_iff₀ hkPosR (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
        calc
          24 * ((m : ℝ) + (blockLayerSlack k : ℝ) + 2) *
                ((w : ℝ) + 2) ^ 2 * ((k : ℝ) + 1) ≤
              24 * ((m : ℝ) + (blockLayerSlack k : ℝ) + 2) *
                ((w : ℝ) + 2) ^ 2 * (2 * (k : ℝ)) :=
            mul_le_mul_of_nonneg_left hkTwo hnum
          _ = 48 * ((m : ℝ) + (blockLayerSlack k : ℝ) + 2) *
                ((w : ℝ) + 2) ^ 2 * (k : ℝ) := by ring
  have hbase : 0 ≤ ((v : ℝ) * Real.log 2) ^ k *
      Real.exp (40 * C / (Real.log 2 * (2 : ℝ) ^ M)) := by positivity
  apply mul_le_mul_of_nonneg_left _ (by
    exact div_nonneg
      (mul_nonneg (sharpBlockLayerScale_pos M).le (by positivity))
      (by positivity))
  calc
    (((v : ℝ) * Real.log 2) ^ k *
          Real.exp (40 * C / (Real.log 2 * (2 : ℝ) ^ M))) *
          smirnovProbability k (m + blockLayerSlack k + 1) v /
            (k.factorial : ℝ) ≤
        (((v : ℝ) * Real.log 2) ^ k *
          Real.exp (40 * C / (Real.log 2 * (2 : ℝ) ^ M))) *
          (48 * ((m : ℝ) + (blockLayerSlack k : ℝ) + 2) *
            ((w : ℝ) + 2) ^ 2 / ((k : ℝ) + 1)) /
            (k.factorial : ℝ) := by gcongr
    _ = ((v : ℝ) * Real.log 2) ^ k *
          Real.exp (40 * C / (Real.log 2 * (2 : ℝ) ^ M)) *
          (48 * ((m : ℝ) + (blockLayerSlack k : ℝ) + 2) *
            ((w : ℝ) + 2) ^ 2) /
          ((k + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp

end Erdos446
