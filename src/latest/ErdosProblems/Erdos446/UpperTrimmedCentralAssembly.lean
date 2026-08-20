/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperTrimmedLowSupportMass
import ErdosProblems.Erdos446.UpperDepthClusterBridge

/-!
# Erdős Problem 446: central-depth sum after trimming

This module completes the finite low-cardinality calculation.  The factor
`2^(k+1)(log 2)^k` produced by the sharp block envelope changes the Poisson
parameter from `K` to `(2 log 2)K`; Ford's central-depth sum then gives the
required combinatorial weight.  The actual smooth support is handled by the
retained/residual partition, and the complementary high-cardinality layers
are exactly the already proved Poisson tail.
-/

namespace Erdos446

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

theorem two_pow_log_mul_centralTerm (K k : ℕ) :
    (2 : ℝ) ^ (k + 1) * Real.log 2 ^ k *
        fordCentralDepthTerm (K : ℝ) K k =
      2 * fordCentralDepthTerm
        ((2 * Real.log 2) * (K : ℝ)) K k := by
  rw [fordCentralDepthTerm, fordCentralDepthTerm,
    fordPoissonFactor, fordPoissonFactor]
  rw [pow_succ, mul_pow]
  ring

/-- The complete retained low-cardinality mass has Ford's central weight. -/
theorem sum_retainedBlockClusterMass_le_weight
    {M K : ℕ} (hK : 8 ≤ K) :
    (∑ k ∈ Finset.range (10 * K + 1),
        retainedBlockClusterMassOver M (compositionsOf K k)) ≤
      sharpBlockLayerScale M *
        (2 * fordWeightedLayerMassConstant * 936) *
          fordCombinatorialWeight K := by
  have hKpos : 0 < K := by omega
  calc
    (∑ k ∈ Finset.range (10 * K + 1),
        retainedBlockClusterMassOver M (compositionsOf K k)) ≤
      ∑ k ∈ Finset.range (10 * K + 1),
        sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) *
          Real.log 2 ^ k *
            (fordWeightedLayerMassConstant *
              fordCentralDepthTerm (K : ℝ) K k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact retainedBlockClusterMassOver_compositions_le_central hKpos
        (by have := Finset.mem_range.mp hk; omega)
    _ = sharpBlockLayerScale M *
        (2 * fordWeightedLayerMassConstant) *
          fordCentralDepthSum
            ((2 * Real.log 2) * (K : ℝ)) K (10 * K + 1) := by
      rw [fordCentralDepthSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      calc
        sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) *
            Real.log 2 ^ k *
              (fordWeightedLayerMassConstant *
                fordCentralDepthTerm (K : ℝ) K k) =
          sharpBlockLayerScale M * fordWeightedLayerMassConstant *
            ((2 : ℝ) ^ (k + 1) * Real.log 2 ^ k *
              fordCentralDepthTerm (K : ℝ) K k) := by ring
        _ = sharpBlockLayerScale M * fordWeightedLayerMassConstant *
            (2 * fordCentralDepthTerm
              ((2 * Real.log 2) * (K : ℝ)) K k) := by
          rw [two_pow_log_mul_centralTerm]
        _ = sharpBlockLayerScale M *
            (2 * fordWeightedLayerMassConstant) *
              fordCentralDepthTerm
                ((2 * Real.log 2) * (K : ℝ)) K k := by ring
    _ ≤ sharpBlockLayerScale M *
        (2 * fordWeightedLayerMassConstant) *
          (936 * fordCombinatorialWeight K) := by
      apply mul_le_mul_of_nonneg_left
      · exact fordCentralDepthSum_two_log_two_mul_le hK
          (by linarith [Real.log_two_gt_d9])
          (by linarith [Real.log_two_lt_d9])
      · exact mul_nonneg (sharpBlockLayerScale_pos M).le
          (mul_nonneg (by norm_num) fordWeightedLayerMassConstant_nonneg)
    _ = sharpBlockLayerScale M *
        (2 * fordWeightedLayerMassConstant * 936) *
          fordCombinatorialWeight K := by ring

/-- Truncating the retained sum earlier can only decrease it. -/
theorem sum_retainedBlockClusterMass_mono
    {M K L : ℕ} (hLK : L ≤ 10 * K) :
    (∑ k ∈ Finset.range (L + 1),
        retainedBlockClusterMassOver M (compositionsOf K k)) ≤
      ∑ k ∈ Finset.range (10 * K + 1),
        retainedBlockClusterMassOver M (compositionsOf K k) := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega))
    (fun k hk hnot ↦ by
      rw [retainedBlockClusterMassOver]
      exact Finset.sum_nonneg fun b hb ↦
        retainedCompositionBlockClusterMass_nonneg M b)

/-- Closed low-layer bound for actual smooth squarefree supports. -/
theorem sum_lowSquarefreeClusterLayers_le_weight
    {C : ℝ} (hC : 0 ≤ C) {J M K P L : ℕ}
    (hJM : J ≤ M)
    (hmass : ∀ j : ℕ, J ≤ j →
      |primeBlockMass j - Real.log 2| ≤ C / (2 : ℝ) ^ j)
    (hK : 8 ≤ K) (hLK : L ≤ 10 * K)
    (hP : primesUpTo P ⊆
      trimmedAuxiliaryPrimePool M K ∪ retainedPrimePool M K) :
    (∑ k ∈ Finset.range (L + 1), squarefreeClusterLayer P k) ≤
      (smallPrimeClusterFactor M *
          Real.exp (4 * (C + 1) / (2 : ℝ) ^ M)) *
        (sharpBlockLayerScale M *
          (2 * fordWeightedLayerMassConstant * 936)) *
            fordCombinatorialWeight K := by
  have hpairs := sum_lowSquarefreeClusterLayers_le_trimmedPairs
    (L := L) hP
  have hpairMass := trimmedLowPairs_clusterMass_le M K L
  have haux := trimmedAuxiliaryClusterFactor_le hC hJM hmass (K := K)
  have hretMono := sum_retainedBlockClusterMass_mono
    (M := M) (K := K) hLK
  have hret := sum_retainedBlockClusterMass_le_weight (M := M) hK
  have hretNonneg : 0 ≤ ∑ k ∈ Finset.range (L + 1),
      retainedBlockClusterMassOver M (compositionsOf K k) := by
    apply Finset.sum_nonneg
    intro k hk
    apply Finset.sum_nonneg
    intro b hb
    exact retainedCompositionBlockClusterMass_nonneg M b
  have hcoefNonneg : 0 ≤ smallPrimeClusterFactor M *
      Real.exp (4 * (C + 1) / (2 : ℝ) ^ M) :=
    mul_nonneg (smallPrimeClusterFactor_nonneg M) (Real.exp_pos _).le
  calc
    (∑ k ∈ Finset.range (L + 1), squarefreeClusterLayer P k) ≤
        ∑ QR ∈ trimmedLowSupportPairs M K L,
          clusterLength ((joinTrimmedSupport QR).prod id) /
            (((joinTrimmedSupport QR).prod id : ℕ) : ℝ) := hpairs
    _ ≤ trimmedAuxiliaryClusterFactor M K *
        (∑ k ∈ Finset.range (L + 1),
          retainedBlockClusterMassOver M (compositionsOf K k)) := hpairMass
    _ ≤ (smallPrimeClusterFactor M *
          Real.exp (4 * (C + 1) / (2 : ℝ) ^ M)) *
        (∑ k ∈ Finset.range (L + 1),
          retainedBlockClusterMassOver M (compositionsOf K k)) :=
      mul_le_mul_of_nonneg_right haux hretNonneg
    _ ≤ (smallPrimeClusterFactor M *
          Real.exp (4 * (C + 1) / (2 : ℝ) ^ M)) *
        (∑ k ∈ Finset.range (10 * K + 1),
          retainedBlockClusterMassOver M (compositionsOf K k)) :=
      mul_le_mul_of_nonneg_left hretMono hcoefNonneg
    _ ≤ (smallPrimeClusterFactor M *
          Real.exp (4 * (C + 1) / (2 : ℝ) ^ M)) *
        (sharpBlockLayerScale M *
          (2 * fordWeightedLayerMassConstant * 936) *
            fordCombinatorialWeight K) :=
      mul_le_mul_of_nonneg_left hret hcoefNonneg
    _ = (smallPrimeClusterFactor M *
          Real.exp (4 * (C + 1) / (2 : ℝ) ^ M)) *
        (sharpBlockLayerScale M *
          (2 * fordWeightedLayerMassConstant * 936)) *
            fordCombinatorialWeight K := by ring

/-- The total squarefree mass is bounded by its layers through `L` plus
the exact complementary tail. -/
theorem squarefreeClusterMass_le_low_add_tail (P L : ℕ) :
    squarefreeClusterMass P ≤
      (∑ k ∈ Finset.range (L + 1), squarefreeClusterLayer P k) +
        ∑ k ∈ Finset.Ioc L (primesUpTo P).card,
          squarefreeClusterLayer P k := by
  rw [squarefreeClusterMass_eq_sum_layers]
  let A := Finset.range ((primesUpTo P).card + 1)
  let B := Finset.range (L + 1)
  let T := Finset.Ioc L (primesUpTo P).card
  have hsub : A ⊆ B ∪ T := by
    intro k hk
    have hkTop := Finset.mem_range.mp hk
    by_cases hkL : k ≤ L
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
    · exact Finset.mem_union_right _
        (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)
  have hdisj : Disjoint B T := by
    rw [Finset.disjoint_left]
    intro k hkB hkT
    have := Finset.mem_range.mp hkB
    have := (Finset.mem_Ioc.mp hkT).1
    omega
  calc
    (∑ k ∈ A, squarefreeClusterLayer P k) ≤
        ∑ k ∈ B ∪ T, squarefreeClusterLayer P k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun k hk hnot ↦ squarefreeClusterLayer_nonneg P k)
    _ = (∑ k ∈ B, squarefreeClusterLayer P k) +
        ∑ k ∈ T, squarefreeClusterLayer P k := by
      rw [Finset.sum_union hdisj]
    _ = _ := rfl

end

end Erdos446
