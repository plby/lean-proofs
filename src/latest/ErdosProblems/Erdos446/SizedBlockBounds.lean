/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SizedCompositions
import ErdosProblems.Erdos446.BlockPartition

/-!
# Erdős Problem 446: product bounds for size-truncated blocks

The real-valued size cost used in the cyclic first-moment argument is exactly
the exponent controlling products of primes from the doubly exponential
blocks.  This file translates that cost into a uniform natural-number bound.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

def compositionSizeCostNat {K : ℕ} (b : Fin K → ℕ) : ℕ :=
  ∑ i : Fin K, b i * 2 ^ i.val

theorem cast_compositionSizeCostNat {K : ℕ} (b : Fin K → ℕ) :
    (compositionSizeCostNat b : ℝ) = compositionSizeCost b := by
  simp [compositionSizeCostNat, compositionSizeCost]

theorem selection_block_product_le {M K : ℕ} {b : Fin K → ℕ}
    {S : Finset ℕ} (hS : S ∈ blockSelectionSets M K (extendComposition b))
    (i : Fin K) :
    (S ∩ primeBlock (M + i)).prod id ≤
      blockEndpoint (M + i + 1) ^ b i := by
  calc
    (S ∩ primeBlock (M + i)).prod id ≤
        (S ∩ primeBlock (M + i)).prod
          (fun _p ↦ blockEndpoint (M + i + 1)) := by
      apply Finset.prod_le_prod'
      intro p hp
      exact (mem_primeBlock.mp (Finset.mem_inter.mp hp).2).2.2
    _ = blockEndpoint (M + i + 1) ^ (S ∩ primeBlock (M + i)).card := by
      rw [Finset.prod_const]
    _ = blockEndpoint (M + i + 1) ^ b i := by
      rw [(mem_blockSelectionSets.mp hS).2 i i.isLt,
        extendComposition_fin]

theorem selectionProduct_le_sizeCostNat {M K : ℕ} {b : Fin K → ℕ}
    {S : Finset ℕ} (hS : S ∈ blockSelectionSets M K (extendComposition b)) :
    S.prod id ≤ 2 ^ (2 ^ (M + 1) * compositionSizeCostNat b) := by
  have hdecomp := selection_eq_biUnion_blocks
    (M := M) (k := K) (S := S) (mem_blockSelectionSets.mp hS).1
  rw [hdecomp, Finset.prod_biUnion (block_inter_pairwiseDisjoint M K S)]
  rw [← Fin.prod_univ_eq_prod_range
    (fun i : ℕ ↦ (S ∩ primeBlock (M + i)).prod id) K]
  calc
    (∏ i : Fin K, (S ∩ primeBlock (M + i)).prod id) ≤
        ∏ i : Fin K, blockEndpoint (M + i + 1) ^ b i := by
      apply Finset.prod_le_prod'
      intro i hi
      exact selection_block_product_le hS i
    _ = 2 ^ (2 ^ (M + 1) * compositionSizeCostNat b) := by
      simp only [blockEndpoint]
      conv_lhs =>
        enter [2, i]
        rw [← pow_mul]
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      simp only [compositionSizeCostNat]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show M + i.val + 1 = (M + 1) + i.val by omega,
        pow_add]
      ring

def fordConstructionBound (M K : ℕ) : ℕ :=
  2 ^ (32 * 2 ^ (M + K))

def fordConstructionScale (M K : ℕ) : ℕ :=
  2 ^ (128 * 2 ^ (M + K))

theorem sizedBlockFamily_le_constructionBound {M K : ℕ}
    {b : Fin K → ℕ} (hb : b ∈ sizedCappedCompositions M K)
    {a : ℕ} (ha : a ∈ compositionBlockFamily M b) :
    a ≤ fordConstructionBound M K := by
  obtain ⟨S, hS, rfl⟩ := mem_blockFamily.mp ha
  have hprod := selectionProduct_le_sizeCostNat hS
  have hcostR := (mem_sizedCappedCompositions.mp hb).2
  have hcost : compositionSizeCostNat b ≤ 16 * 2 ^ K := by
    exact_mod_cast cast_compositionSizeCostNat b ▸ hcostR
  have hexp : 2 ^ (M + 1) * compositionSizeCostNat b ≤
      32 * 2 ^ (M + K) := by
    calc
      2 ^ (M + 1) * compositionSizeCostNat b ≤
          2 ^ (M + 1) * (16 * 2 ^ K) :=
        Nat.mul_le_mul_left _ hcost
      _ = 32 * 2 ^ (M + K) := by
        rw [pow_add, pow_succ]
        ring
  exact hprod.trans (by
    dsimp [fordConstructionBound]
    exact Nat.pow_le_pow_right (by omega) hexp)

theorem fordConstructionScale_eq_pow (M K : ℕ) :
    fordConstructionScale M K = fordConstructionBound M K ^ 4 := by
  change 2 ^ (128 * 2 ^ (M + K)) =
    (2 ^ (32 * 2 ^ (M + K))) ^ 4
  rw [← pow_mul]
  congr 1
  ring

theorem fordConstructionBound_one_lt (M K : ℕ) :
    1 < fordConstructionBound M K := by
  dsimp [fordConstructionBound]
  exact Nat.one_lt_pow (by positivity) (by omega)

theorem fordConstructionBound_sq_lt_scale (M K : ℕ) :
    fordConstructionBound M K * fordConstructionBound M K <
      fordConstructionScale M K := by
  rw [fordConstructionScale_eq_pow]
  simpa [pow_two] using
    Nat.pow_lt_pow_right (fordConstructionBound_one_lt M K) (by omega : 2 < 4)

theorem fordConstructionBound_le_two_scale (M K : ℕ) :
    fordConstructionBound M K ≤ 2 * fordConstructionScale M K := by
  rw [fordConstructionScale_eq_pow]
  have hB : 1 ≤ fordConstructionBound M K :=
    (fordConstructionBound_one_lt M K).le
  have hpow : fordConstructionBound M K ^ 1 ≤
      fordConstructionBound M K ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  simpa using hpow.trans (Nat.le_mul_of_pos_left _ (by omega : 0 < 2))

theorem sizedBlockFamily_scale {N M K : ℕ}
    (hNB : N ≤ fordConstructionBound M K)
    {b : Fin K → ℕ} (hb : b ∈ sizedCappedCompositions M K)
    {a : ℕ} (ha : a ∈ compositionBlockFamily M b) {d : ℕ}
    (hd : d ∈ a.divisors) :
    N ≤ fordConstructionScale M K / d ∧
      fordConstructionScale M K ≤
        (fordConstructionScale M K / d) ^ 2 := by
  let B := fordConstructionBound M K
  let y := fordConstructionScale M K
  have hB : 1 < B := fordConstructionBound_one_lt M K
  have haB : a ≤ B := sizedBlockFamily_le_constructionBound hb ha
  have haPos : 0 < a := blockFamily_pos ha
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
  have hda : d ≤ a := Nat.le_of_dvd haPos (Nat.dvd_of_mem_divisors hd)
  have hdB : d ≤ B := hda.trans haB
  have hy : y = B ^ 4 := fordConstructionScale_eq_pow M K
  have hB3d : B ^ 3 * d ≤ y := by
    rw [hy, show B ^ 4 = B ^ 3 * B by ring]
    exact Nat.mul_le_mul_left _ hdB
  have hquot : B ^ 3 ≤ y / d :=
    (Nat.le_div_iff_mul_le hdPos).2 hB3d
  constructor
  · exact hNB.trans (by
      have hBB3 : B ≤ B ^ 3 := by
        simpa using Nat.pow_le_pow_right (by omega : 0 < B) (by omega : 1 ≤ 3)
      exact hBB3.trans hquot)
  · calc
      y = B ^ 4 := hy
      _ ≤ B ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
      _ = (B ^ 3) ^ 2 := by simpa using pow_mul B 3 2
      _ ≤ (y / d) ^ 2 := Nat.pow_le_pow_left hquot 2

theorem sizedBlockFamily_scale_of_le {N M K y : ℕ}
    (hNB : N ≤ fordConstructionBound M K)
    (hy : fordConstructionScale M K ≤ y)
    {b : Fin K → ℕ} (hb : b ∈ sizedCappedCompositions M K)
    {a : ℕ} (ha : a ∈ compositionBlockFamily M b) {d : ℕ}
    (hd : d ∈ a.divisors) :
    N ≤ y / d ∧ y ≤ (y / d) ^ 2 := by
  let B := fordConstructionBound M K
  let q := y / d
  have hB : 2 ≤ B := fordConstructionBound_one_lt M K
  have haB : a ≤ B := sizedBlockFamily_le_constructionBound hb ha
  have haPos : 0 < a := blockFamily_pos ha
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdB : d ≤ B :=
    (Nat.le_of_dvd haPos (Nat.dvd_of_mem_divisors hd)).trans haB
  have hscale : fordConstructionScale M K = B ^ 4 :=
    fordConstructionScale_eq_pow M K
  have hB3d : B ^ 3 * d ≤ y := by
    calc
      B ^ 3 * d ≤ B ^ 3 * B := Nat.mul_le_mul_left _ hdB
      _ = fordConstructionScale M K := by rw [hscale]; ring
      _ ≤ y := hy
  have hq : B ^ 3 ≤ q := (Nat.le_div_iff_mul_le hdPos).2 hB3d
  have hNB3 : N ≤ B ^ 3 := hNB.trans (by
    simpa using Nat.pow_le_pow_right (by omega : 0 < B) (by omega : 1 ≤ 3))
  constructor
  · exact hNB3.trans hq
  · have hylt : y < (q + 1) * d := by
      simpa [q, mul_comm] using Nat.lt_mul_div_succ y hdPos
    have htwoB : 2 * B ≤ B ^ 3 := by
      have h2sq : 2 ≤ B ^ 2 := by
        have : 2 ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hB 2
        omega
      calc
        2 * B ≤ B ^ 2 * B := Nat.mul_le_mul_right B h2sq
        _ = B ^ 3 := by ring
    have htwoBq : 2 * B ≤ q := htwoB.trans hq
    have hqpos : 1 ≤ q := le_trans (by omega : 1 ≤ B ^ 3) hq
    have hBqB : B ≤ q * B := by
      simpa using Nat.mul_le_mul_right B hqpos
    have htwoqB : 2 * (q * B) ≤ q * q := by
      have := Nat.mul_le_mul_left q htwoBq
      nlinarith
    have hqBsq : (q + 1) * B ≤ q ^ 2 := by
      rw [pow_two]
      nlinarith
    exact (le_of_lt hylt).trans <|
      (Nat.mul_le_mul_left (q + 1) hdB).trans hqBsq

end Erdos446
