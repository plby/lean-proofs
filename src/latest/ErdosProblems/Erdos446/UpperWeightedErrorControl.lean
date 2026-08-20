/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperExceptionalKthConcrete

/-!
# Erdős Problem 446: nonuniform block errors on the weighted T-set

The weighted prefix barrier itself gives a coordinate cap depending only on
the layer depth, not on the total number of selected primes.  This removes
the artificial condition `k + blockLayerSlack k < 2^M` from the raw
prime-block estimate.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

private theorem succ_le_two_pow_half {n : ℕ} (hn : 6 ≤ n) :
    n + 1 ≤ 2 ^ (n / 2) := by
  induction n using Nat.twoStepInduction with
  | zero => omega
  | one => omega
  | more n ih ih' =>
      by_cases hn' : 6 ≤ n
      · have hhalf : (n + 2) / 2 = n / 2 + 1 := by omega
        rw [hhalf]
        calc
          n + 2 + 1 ≤ 2 * (n + 1) := by omega
          _ ≤ 2 * 2 ^ (n / 2) := Nat.mul_le_mul_left 2 (ih hn')
          _ = 2 ^ (n / 2 + 1) := by rw [pow_succ]; ring
      · have hnsmall : n ≤ 5 := by omega
        have hn4 : 4 ≤ n := by omega
        interval_cases n <;> norm_num

/-- A weighted prefix cannot contain substantially more than twice its
affine depth.  The constant six makes the elementary half-exponent estimate
valid in every small case. -/
theorem blockPrefixCount_le_of_fordWeightedBarrier
    {v γ : ℕ} {c : Fin v → ℕ}
    (hc : SatisfiesFordWeightedBarrier γ c) {q : ℕ} (hq : q ≤ v) :
    blockPrefixCount c q ≤ 2 * (γ + q) + 5 := by
  let N := blockPrefixCount c q
  by_contra hnot
  have hNlarge : 2 * (γ + q) + 6 ≤ N := by omega
  have hN6 : 6 ≤ N := by omega
  have hhalf := succ_le_two_pow_half hN6
  have hW := blockPrefixWeight_le_count_mul_pow c q
  have hone : 1 ≤ 2 ^ q := one_le_pow₀ (by omega)
  have hW' : blockPrefixWeight c q + 1 ≤ (N + 1) * 2 ^ q := by
    dsimp [N] at hW ⊢
    nlinarith
  have hbar := hc q (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))
  have hupper :
      2 ^ N ≤ 2 ^ (γ + q + N / 2) := by
    calc
      2 ^ N ≤ 2 ^ γ * (blockPrefixWeight c q + 1) := by
        simpa only [N] using hbar
      _ ≤ 2 ^ γ * ((N + 1) * 2 ^ q) :=
        Nat.mul_le_mul_left _ hW'
      _ ≤ 2 ^ γ * (2 ^ (N / 2) * 2 ^ q) := by
        exact Nat.mul_le_mul_left _
          (Nat.mul_le_mul_right (2 ^ q) hhalf)
      _ = 2 ^ (γ + q + N / 2) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
  have hexp : γ + q + N / 2 < N := by omega
  have := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hupper
  omega

/-- Coordinate cap for a weighted Ford occupancy.  Crucially the factor is
`2γ+7`, independent of `k` and `v`. -/
theorem fordWeightedOccupancy_linear_cap
    {k v γ : ℕ} {c : Fin v → ℕ}
    (hc : c ∈ fordWeightedOccupancies k v γ) (i : Fin v) :
    extendComposition c i ≤ (2 * γ + 7) * (i.val + 1) := by
  rw [extendComposition_fin]
  have hcoord := occupancyCoordinate_le_prefix_succ c i
  have hpref := blockPrefixCount_le_of_fordWeightedBarrier
    (mem_fordWeightedOccupancies.mp hc).2 (show i.val + 1 ≤ v by omega)
  rw [blockPrefixCount_eq_occupancyPrefix c (show i.val + 1 ≤ v by omega)]
    at hpref
  calc
    c i ≤ occupancyPrefix c (i.val + 1) := hcoord
    _ ≤ 2 * (γ + (i.val + 1)) + 5 := hpref
    _ ≤ (2 * γ + 7) * (i.val + 1) := by
      nlinarith [Nat.zero_le ((2 * γ + 7) * i.val)]

/-- The repeated-slot Mertens error on a weighted Ford set is geometrically
summable with a constant linear in its layer depth. -/
theorem fordWeightedSlotGeometricError_sum_le
    {M k v γ : ℕ} {c : Fin v → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hc : c ∈ fordWeightedOccupancies k v γ) :
    (∑ s : BlockSlot v (extendComposition c),
        C / (2 : ℝ) ^ (M + s.1.val)) ≤
      4 * (2 * γ + 7) * C / (2 : ℝ) ^ M := by
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    (slot_geometric_error_sum_le
      (M := M) (k := v) (K := 2 * γ + 7) (b := extendComposition c)
      hC (fordWeightedOccupancy_linear_cap hc))

/-- Product of the actual block masses over a weighted Ford occupancy. -/
theorem fordWeightedBlockMassPowerProduct_upper
    {M k v γ : ℕ} {c : Fin v → ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hc : c ∈ fordWeightedOccupancies k v γ)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val)) :
    (∏ i : Fin v, primeBlockMass (M + i) ^ c i) ≤
      Real.log 2 ^ k *
        Real.exp (4 * (2 * γ + 7) * (C / Real.log 2) /
          (2 : ℝ) ^ M) := by
  let z : BlockSlot v (extendComposition c) → ℝ :=
    blockMassRelativeError C M c
  have hz0 : ∀ s, 0 ≤ z s :=
    fun s ↦ blockMassRelativeError_nonneg hC M c s
  have hp := prod_upper_of_relative_error
    (Real.log 2) (Real.log_pos one_lt_two).le
    (fun s : BlockSlot v (extendComposition c) ↦
      primeBlockMass (M + s.1)) z
    (fun s ↦ primeBlockMass_nonneg _) hz0
    (primeBlockMass_upper_relative hmass)
  have hcard : Fintype.card (BlockSlot v (extendComposition c)) = k := by
    rw [card_blockSlot, slotCount]
    simp only [extendComposition_fin]
    exact (mem_fordWeightedOccupancies.mp hc).1
  rw [hcard] at hp
  have hsum : (∑ s, z s) ≤
      4 * (2 * γ + 7) * (C / Real.log 2) / (2 : ℝ) ^ M := by
    simpa only [z, blockMassRelativeError, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat] using
        fordWeightedSlotGeometricError_sum_le
          (M := M) (C := C / Real.log 2) (by positivity) hc
  calc
    (∏ i : Fin v, primeBlockMass (M + i) ^ c i) =
        ∏ s : BlockSlot v (extendComposition c),
          primeBlockMass (M + s.1) := by
      simpa only [extendComposition_fin] using
        (prod_blockSlot_fiber
          (k := v) (b := extendComposition c)
          (fun i : Fin v ↦ primeBlockMass (M + i))).symm
    _ ≤ Real.log 2 ^ k * Real.exp (∑ s, z s) := hp
    _ ≤ Real.log 2 ^ k *
        Real.exp (4 * (2 * γ + 7) * (C / Real.log 2) /
          (2 : ℝ) ^ M) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum) (by positivity)

/-- A proper subset of the weighted Ford set retains its own
reciprocal-factorial mass under the exact nonuniform block weights. -/
theorem blockClusterMassOver_le_fordWeightedMass_nonuniform
    {M k v γ : ℕ} {I : Finset (Fin v → ℕ)} {C A : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hI : I ⊆ fordWeightedOccupancies k v γ)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (henvelope : ∀ c ∈ I, ∀ a ∈ compositionBlockFamily M c,
      clusterLength a ≤ A) :
    blockClusterMassOver M I ≤
      A * Real.log 2 ^ k *
        Real.exp (4 * (2 * γ + 7) * (C / Real.log 2) /
          (2 : ℝ) ^ M) * reciprocalFactorialMassOver I := by
  rw [blockClusterMassOver, reciprocalFactorialMassOver, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  have hbase := blockFamily_reciprocal_sum_upper M v (extendComposition c)
  have hprod := fordWeightedBlockMassPowerProduct_upper hC (hI hc) hmass
  have hrecip :
      (∑ a ∈ compositionBlockFamily M c, 1 / (a : ℝ)) ≤
        (Real.log 2 ^ k *
          Real.exp (4 * (2 * γ + 7) * (C / Real.log 2) /
            (2 : ℝ) ^ M)) / compositionFactorial c := by
    calc
      (∑ a ∈ compositionBlockFamily M c, 1 / (a : ℝ)) ≤
          ∏ i : Fin v,
            primeBlockMass (M + i) ^ c i / ((c i).factorial : ℝ) := by
        simpa only [compositionBlockFamily, extendComposition_fin] using hbase
      _ = (∏ i : Fin v, primeBlockMass (M + i) ^ c i) /
            compositionFactorial c := by
        rw [Finset.prod_div_distrib]
        rfl
      _ ≤ (Real.log 2 ^ k *
          Real.exp (4 * (2 * γ + 7) * (C / Real.log 2) /
            (2 : ℝ) ^ M)) / compositionFactorial c :=
        div_le_div_of_nonneg_right hprod (by
          dsimp [compositionFactorial]
          positivity)
  calc
    compositionBlockClusterMass M c ≤
        A * (∑ a ∈ compositionBlockFamily M c, 1 / (a : ℝ)) := by
      rw [compositionBlockClusterMass]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a ha
      rw [div_eq_mul_inv]
      simpa [one_div] using
        mul_le_mul_of_nonneg_right (henvelope c hc a ha)
          (show 0 ≤ ((a : ℝ)⁻¹) by positivity)
    _ ≤ A * ((Real.log 2 ^ k *
          Real.exp (4 * (2 * γ + 7) * (C / Real.log 2) /
            (2 : ℝ) ^ M)) / compositionFactorial c) :=
      mul_le_mul_of_nonneg_left hrecip hA
    _ = A * Real.log 2 ^ k *
        Real.exp (4 * (2 * γ + 7) * (C / Real.log 2) /
          (2 : ℝ) ^ M) * (1 / compositionFactorial c) := by ring

/-- Raw arithmetic estimate on a canonical layer, with no k-dependent
offset assumption. -/
theorem blockIntegerDyadicLayer_mass_le_fordWeightedMass_nonuniform
    {M k v γ : ℕ} {C R : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ i : Fin v,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hford : reciprocalFactorialMassOver
      (fordWeightedOccupancies k v γ) ≤ R) :
    blockClusterMassOver M (blockIntegerDyadicLayer k v γ) ≤
      (sharpBlockLayerScale M * (2 : ℝ) ^ (k - γ + 1)) *
        Real.log 2 ^ k *
          Real.exp (4 * (2 * γ + 7) * (C / Real.log 2) /
            (2 : ℝ) ^ M) * R := by
  let A : ℝ := sharpBlockLayerScale M * (2 : ℝ) ^ (k - γ + 1)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (sharpBlockLayerScale_pos M).le (by positivity)
  have hraw := blockClusterMassOver_le_fordWeightedMass_nonuniform
    hC hA (blockIntegerDyadicLayer_subset_fordWeightedOccupancies k v γ)
    hmass (fun c hc a ha ↦ blockIntegerDyadicLayer_clusterLength_le hc ha)
  have hset : reciprocalFactorialMassOver
      (blockIntegerDyadicLayer k v γ) ≤ R :=
    (reciprocalFactorialMassOver_mono
      (blockIntegerDyadicLayer_subset_fordWeightedOccupancies k v γ)).trans
        hford
  exact hraw.trans (mul_le_mul_of_nonneg_left hset (by
    dsimp [A]
    positivity))

end Erdos446
