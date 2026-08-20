/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperBlockEnvelope
import ErdosProblems.Erdos446.SmirnovPykeBounds

/-!
# Erdős Problem 446: finite dyadic layers of the block envelope

This file proves the elementary, but important, passage from a dyadic layer
of Ford's prefix envelope to a single finite Smirnov barrier.  The harmless
logarithmic slack is chosen to be

`(Nat.log 2 (k + 1)).succ`.

It is small enough for the final geometric layer sum, while the inequalities

`k + 1 < 2 ^ slack` and `2 ^ slack ≤ 2 * (k + 1)`

make the barrier proof completely integral.  No ordered-simplex or
measure-theoretic approximation is used here.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The logarithmic number of extra occupied cells needed when a weighted
prefix is replaced by the coarser bound `k * 2^h`. -/
def blockLayerSlack (k : ℕ) : ℕ := (Nat.log 2 (k + 1)).succ

theorem add_one_lt_two_pow_blockLayerSlack (k : ℕ) :
    k + 1 < 2 ^ blockLayerSlack k := by
  exact Nat.lt_pow_succ_log_self (by norm_num) (k + 1)

theorem two_pow_blockLayerSlack_le (k : ℕ) :
    2 ^ blockLayerSlack k ≤ 2 * (k + 1) := by
  rw [blockLayerSlack, pow_succ]
  simpa only [Nat.succ_eq_add_one, mul_comm] using
    Nat.mul_le_mul_left 2
      (Nat.pow_log_le_self 2 (Nat.succ_ne_zero k))

/-- The positive scale separated from the normalized prefix envelope. -/
noncomputable def sharpBlockLayerScale (M : ℕ) : ℝ :=
  (2 : ℝ) ^ (M + 1) * Real.log 2

theorem sharpBlockLayerScale_pos (M : ℕ) :
    0 < sharpBlockLayerScale M := by
  dsimp [sharpBlockLayerScale]
  positivity

/-- A half-open dyadic layer of the sharp block envelope.  After division by
`2^k`, this is exactly the usual layer `[2^-m,2^(1-m))`. -/
noncomputable def sharpBlockDyadicLayer (M k v m : ℕ) :
    Finset (Fin v → ℕ) :=
  (compositionsOf v k).filter fun b ↦
    sharpBlockLayerScale M * (2 : ℝ) ^ k / (2 : ℝ) ^ m ≤
        blockClusterSharpEnvelope M k b ∧
      blockClusterSharpEnvelope M k b <
        sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m

theorem mem_sharpBlockDyadicLayer {M k v m : ℕ} {b : Fin v → ℕ} :
    b ∈ sharpBlockDyadicLayer M k v m ↔
      (∑ i, b i = k) ∧
      sharpBlockLayerScale M * (2 : ℝ) ^ k / (2 : ℝ) ^ m ≤
          blockClusterSharpEnvelope M k b ∧
      blockClusterSharpEnvelope M k b <
          sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m := by
  simp [sharpBlockDyadicLayer, mem_compositionsOf]

theorem blockClusterSharpEnvelope_le_prefix
    (M k : ℕ) {v : ℕ} (b : Fin v → ℕ) {h : ℕ} (hh : h ≤ v) :
    blockClusterSharpEnvelope M k b ≤
      blockClusterSharpPrefixEnvelope M k b h := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr
    ⟨h, Finset.mem_range.mpr (by omega), rfl⟩

/-- The sharp prefix is at most the separated scale times its normalized
integer prefix expression. -/
theorem blockClusterSharpPrefixEnvelope_le_scaled
    (M k : ℕ) {v : ℕ} (b : Fin v → ℕ) (h : ℕ) :
    blockClusterSharpPrefixEnvelope M k b h ≤
      sharpBlockLayerScale M *
        ((2 : ℝ) ^ (k - blockPrefixCount b h) *
          (blockPrefixWeight b h + 1 : ℕ)) := by
  let s : ℝ := (2 : ℝ) ^ (M + 1)
  let W : ℝ := (blockPrefixWeight b h : ℝ)
  have hs : 1 ≤ s := by
    dsimp [s]
    exact one_le_pow₀ (by norm_num)
  have hW : 0 ≤ W := by positivity
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hinside : (s * W + 1) * Real.log 2 ≤
      s * Real.log 2 * (W + 1) := by
    have : s * W + 1 ≤ s * (W + 1) := by nlinarith
    calc
      (s * W + 1) * Real.log 2 ≤
          (s * (W + 1)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right this hlog
      _ = s * Real.log 2 * (W + 1) := by ring
  rw [blockClusterSharpPrefixEnvelope, sharpBlockLayerScale]
  simp only [Nat.cast_add, Nat.cast_one]
  change (2 : ℝ) ^ (k - blockPrefixCount b h) *
      (((2 : ℝ) ^ (M + 1) * (blockPrefixWeight b h : ℝ) + 1) *
        Real.log 2) ≤
    ((2 : ℝ) ^ (M + 1) * Real.log 2) *
      ((2 : ℝ) ^ (k - blockPrefixCount b h) *
        ((blockPrefixWeight b h : ℝ) + 1))
  simpa only [s, W] using (show
    (2 : ℝ) ^ (k - blockPrefixCount b h) *
        ((s * W + 1) * Real.log 2) ≤
      (s * Real.log 2) *
        ((2 : ℝ) ^ (k - blockPrefixCount b h) * (W + 1)) from by
    calc
      (2 : ℝ) ^ (k - blockPrefixCount b h) *
          ((s * W + 1) * Real.log 2) ≤
        (2 : ℝ) ^ (k - blockPrefixCount b h) *
          (s * Real.log 2 * (W + 1)) :=
        mul_le_mul_of_nonneg_left hinside (by positivity)
      _ = _ := by ring)

theorem blockPrefixCount_le_total
    {v : ℕ} (b : Fin v → ℕ) {k h : ℕ}
    (hb : ∑ i, b i = k) (hh : h ≤ v) :
    blockPrefixCount b h ≤ k := by
  rw [blockPrefixCount_eq_occupancyPrefix b hh, ← hb]
  rw [← occupancyPrefix_at_length b]
  exact occupancyPrefix_mono b hh

/-- The endpoint-weighted prefix is no larger than the number of selected
primes times the right endpoint weight. -/
theorem blockPrefixWeight_le_count_mul_pow
    {v : ℕ} (b : Fin v → ℕ) (h : ℕ) :
    blockPrefixWeight b h ≤ blockPrefixCount b h * 2 ^ h := by
  rw [blockPrefixWeight, blockPrefixCount]
  calc
    (∑ i ∈ Finset.range h, extendComposition b i * 2 ^ i) ≤
        ∑ i ∈ Finset.range h, extendComposition b i * 2 ^ h := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by omega) (Finset.mem_range.mp hi).le)
    _ = (∑ i ∈ Finset.range h, extendComposition b i) * 2 ^ h := by
      rw [Finset.sum_mul]

/-- The lower edge of a dyadic layer forces the integral power barrier
`2^(prefix count) ≤ 2^m (prefix weight + 1)`. -/
theorem sharpBlockDyadicLayer_powerBarrier
    {M k v m : ℕ} {b : Fin v → ℕ}
    (hb : b ∈ sharpBlockDyadicLayer M k v m) {h : ℕ} (hh : h ≤ v) :
    2 ^ blockPrefixCount b h ≤
      2 ^ m * (blockPrefixWeight b h + 1) := by
  have hbData := mem_sharpBlockDyadicLayer.mp hb
  have hcount : blockPrefixCount b h ≤ k :=
    blockPrefixCount_le_total b hbData.1 hh
  have hchain :
      sharpBlockLayerScale M * (2 : ℝ) ^ k / (2 : ℝ) ^ m ≤
        sharpBlockLayerScale M *
          ((2 : ℝ) ^ (k - blockPrefixCount b h) *
            (blockPrefixWeight b h + 1 : ℕ)) :=
    hbData.2.1.trans <|
      (blockClusterSharpEnvelope_le_prefix M k b hh).trans
        (blockClusterSharpPrefixEnvelope_le_scaled M k b h)
  have hscale : 0 < sharpBlockLayerScale M := sharpBlockLayerScale_pos M
  have hpowm : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hmul :
      sharpBlockLayerScale M * (2 : ℝ) ^ k ≤
        (sharpBlockLayerScale M *
          ((2 : ℝ) ^ (k - blockPrefixCount b h) *
            (blockPrefixWeight b h + 1 : ℕ))) * (2 : ℝ) ^ m :=
    (div_le_iff₀ hpowm).mp hchain
  have hcancelScale :
      (2 : ℝ) ^ k ≤
        ((2 : ℝ) ^ (k - blockPrefixCount b h) *
          (blockPrefixWeight b h + 1 : ℕ)) * (2 : ℝ) ^ m := by
    have hs := hmul
    ring_nf at hs
    nlinarith
  have hpowSplit :
      (2 : ℝ) ^ k =
        (2 : ℝ) ^ (k - blockPrefixCount b h) *
          (2 : ℝ) ^ blockPrefixCount b h := by
    rw [← pow_add, Nat.sub_add_cancel hcount]
  rw [hpowSplit] at hcancelScale
  have hleft : (0 : ℝ) <
      (2 : ℝ) ^ (k - blockPrefixCount b h) := by positivity
  have hcancelPower :
      (2 : ℝ) ^ blockPrefixCount b h ≤
        (blockPrefixWeight b h + 1 : ℕ) * (2 : ℝ) ^ m := by
    have hs := hcancelScale
    ring_nf at hs
    nlinarith
  have hcancelPower' :
      (2 : ℝ) ^ blockPrefixCount b h ≤
        (2 : ℝ) ^ m * (blockPrefixWeight b h + 1 : ℕ) := by
    simpa only [mul_comm] using hcancelPower
  exact_mod_cast hcancelPower'

/-- Every genuine dyadic layer lies in one explicit Smirnov occupancy
family.  This is the finite layer/barrier inclusion used in the upper
bound. -/
theorem sharpBlockDyadicLayer_subset_smirnov
    (M k v m : ℕ) :
    sharpBlockDyadicLayer M k v m ⊆
      smirnovOccupancies k (m + blockLayerSlack k) v := by
  intro b hb
  have hbData := mem_sharpBlockDyadicLayer.mp hb
  rw [mem_smirnovOccupancies]
  refine ⟨hbData.1, ?_⟩
  intro h hh hvh
  let C := blockPrefixCount b h
  let W := blockPrefixWeight b h
  have hbarrier : 2 ^ C ≤ 2 ^ m * (W + 1) := by
    simpa [C, W] using sharpBlockDyadicLayer_powerBarrier hb hvh
  have hCk : C ≤ k := by
    exact blockPrefixCount_le_total b hbData.1 hvh
  have hW : W ≤ C * 2 ^ h := by
    exact blockPrefixWeight_le_count_mul_pow b h
  have hWcoarse : W + 1 ≤ (k + 1) * 2 ^ h := by
    have hp : 1 ≤ 2 ^ h := one_le_pow₀ (by omega)
    have hmul : C * 2 ^ h ≤ k * 2 ^ h := Nat.mul_le_mul_right _ hCk
    calc
      W + 1 ≤ C * 2 ^ h + 1 := Nat.add_le_add_right hW 1
      _ ≤ k * 2 ^ h + 2 ^ h := Nat.add_le_add hmul hp
      _ = (k + 1) * 2 ^ h := by ring
  have hpowSlack := add_one_lt_two_pow_blockLayerSlack k
  have hstrict :
      2 ^ m * (W + 1) <
        2 ^ (m + h + blockLayerSlack k) := by
    calc
      2 ^ m * (W + 1) ≤ 2 ^ m * ((k + 1) * 2 ^ h) :=
        Nat.mul_le_mul_left _ hWcoarse
      _ = 2 ^ (m + h) * (k + 1) := by
        rw [pow_add]
        ring
      _ < 2 ^ (m + h) * 2 ^ blockLayerSlack k :=
        Nat.mul_lt_mul_of_pos_left hpowSlack (by positivity)
      _ = 2 ^ (m + h + blockLayerSlack k) := by rw [← pow_add]
  have hpowlt : 2 ^ C < 2 ^ (m + h + blockLayerSlack k) :=
    hbarrier.trans_lt hstrict
  have hClt : C < m + h + blockLayerSlack k :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpowlt
  change blockPrefixCount b h < m + h + blockLayerSlack k at hClt
  rw [blockPrefixCount_eq_occupancyPrefix b hvh] at hClt
  omega

/-- The upper edge of a layer gives a uniform cluster envelope for every
block family represented in that layer. -/
theorem sharpBlockDyadicLayer_clusterLength_le
    {M k v m : ℕ} {b : Fin v → ℕ}
    (hb : b ∈ sharpBlockDyadicLayer M k v m)
    {a : ℕ} (ha : a ∈ compositionBlockFamily M b) :
    clusterLength a ≤
      sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m := by
  have hbData := mem_sharpBlockDyadicLayer.mp hb
  exact (compositionBlock_clusterLength_le_sharpEnvelope hbData.1 ha).trans
    hbData.2.2.le

/-! ## An exact finite partition by the integral prefix envelope -/

/-- The normalized integral prefix expression.  The real sharp prefix
envelope is at most `sharpBlockLayerScale M` times this integer. -/
def blockIntegerPrefixEnvelope
    (k : ℕ) {v : ℕ} (b : Fin v → ℕ) (h : ℕ) : ℕ :=
  2 ^ (k - blockPrefixCount b h) * (blockPrefixWeight b h + 1)

/-- The minimum normalized integral prefix envelope. -/
def blockIntegerEnvelope (k : ℕ) {v : ℕ} (b : Fin v → ℕ) : ℕ :=
  ((Finset.range (v + 1)).image (blockIntegerPrefixEnvelope k b)).min'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

theorem blockIntegerEnvelope_le_prefix
    (k : ℕ) {v : ℕ} (b : Fin v → ℕ) {h : ℕ} (hh : h ≤ v) :
    blockIntegerEnvelope k b ≤ blockIntegerPrefixEnvelope k b h := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr
    ⟨h, Finset.mem_range.mpr (by omega), rfl⟩

theorem blockIntegerPrefixEnvelope_pos
    (k : ℕ) {v : ℕ} (b : Fin v → ℕ) (h : ℕ) :
    0 < blockIntegerPrefixEnvelope k b h := by
  dsimp [blockIntegerPrefixEnvelope]
  positivity

theorem blockIntegerEnvelope_pos
    (k : ℕ) {v : ℕ} (b : Fin v → ℕ) :
    0 < blockIntegerEnvelope k b := by
  let S : Finset ℕ :=
    (Finset.range (v + 1)).image (blockIntegerPrefixEnvelope k b)
  have hS : S.Nonempty := Finset.image_nonempty.mpr
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ v)⟩
  rw [blockIntegerEnvelope]
  change 0 < S.min' hS
  obtain ⟨h, hh, heq⟩ := Finset.mem_image.mp
    (Finset.min'_mem S hS)
  rw [← heq]
  exact blockIntegerPrefixEnvelope_pos k b h

theorem blockIntegerEnvelope_le_two_pow
    (k : ℕ) {v : ℕ} (b : Fin v → ℕ) :
    blockIntegerEnvelope k b ≤ 2 ^ k := by
  have h := blockIntegerEnvelope_le_prefix k b (h := 0) (Nat.zero_le v)
  simpa [blockIntegerPrefixEnvelope, blockPrefixCount, blockPrefixWeight]
    using h

/-- Every arithmetic block family is controlled by the integral envelope,
with the prime-block scale separated out. -/
theorem compositionBlock_clusterLength_le_scaledIntegerEnvelope
    {M k v : ℕ} {b : Fin v → ℕ}
    (hb : ∑ i : Fin v, b i = k) {a : ℕ}
    (ha : a ∈ compositionBlockFamily M b) :
    clusterLength a ≤
      sharpBlockLayerScale M * (blockIntegerEnvelope k b : ℝ) := by
  have hcluster := compositionBlock_clusterLength_le_sharpEnvelope hb ha
  rw [blockIntegerEnvelope]
  let S := (Finset.range (v + 1)).image (blockIntegerPrefixEnvelope k b)
  have hS : S.Nonempty := Finset.image_nonempty.mpr ⟨0, by simp⟩
  obtain ⟨h, hh, heq⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
  have hvh : h ≤ v := Nat.le_of_lt_succ (Finset.mem_range.mp hh)
  have hsharp := blockClusterSharpEnvelope_le_prefix M k b hvh
  have hscaled := blockClusterSharpPrefixEnvelope_le_scaled M k b h
  calc
    clusterLength a ≤ blockClusterSharpEnvelope M k b := hcluster
    _ ≤ blockClusterSharpPrefixEnvelope M k b h := hsharp
    _ ≤ sharpBlockLayerScale M *
        ((blockIntegerPrefixEnvelope k b h : ℕ) : ℝ) := by
      simpa [blockIntegerPrefixEnvelope] using hscaled
    _ = sharpBlockLayerScale M *
        (((S.min' hS : ℕ) : ℝ)) := by rw [heq]

/-- Exact finite dyadic layer of the integral envelope.  Only indices
`m ≤ k` are needed. -/
def blockIntegerDyadicLayer (k v m : ℕ) : Finset (Fin v → ℕ) :=
  (compositionsOf v k).filter fun b ↦
    2 ^ (k - m) ≤ blockIntegerEnvelope k b ∧
      blockIntegerEnvelope k b < 2 ^ (k - m + 1)

theorem mem_blockIntegerDyadicLayer {k v m : ℕ} {b : Fin v → ℕ} :
    b ∈ blockIntegerDyadicLayer k v m ↔
      (∑ i, b i = k) ∧
      2 ^ (k - m) ≤ blockIntegerEnvelope k b ∧
      blockIntegerEnvelope k b < 2 ^ (k - m + 1) := by
  simp [blockIntegerDyadicLayer, mem_compositionsOf]

/-- Canonical layer index obtained from the binary logarithm of the positive
integer envelope. -/
def blockIntegerLayerIndex (k : ℕ) {v : ℕ} (b : Fin v → ℕ) : ℕ :=
  k - Nat.log 2 (blockIntegerEnvelope k b)

theorem blockIntegerLayerIndex_le
    (k : ℕ) {v : ℕ} (b : Fin v → ℕ) :
    blockIntegerLayerIndex k b ≤ k := Nat.sub_le _ _

/-- The canonical index really partitions every composition into one of the
`k+1` finite dyadic layers. -/
theorem mem_blockIntegerDyadicLayer_index
    {k v : ℕ} {b : Fin v → ℕ} (hb : ∑ i, b i = k) :
    b ∈ blockIntegerDyadicLayer k v (blockIntegerLayerIndex k b) := by
  rw [mem_blockIntegerDyadicLayer]
  refine ⟨hb, ?_⟩
  let A := blockIntegerEnvelope k b
  have hApos : 0 < A := blockIntegerEnvelope_pos k b
  have hAle : A ≤ 2 ^ k := blockIntegerEnvelope_le_two_pow k b
  have hlogle : Nat.log 2 A ≤ k := by
    apply (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp
    exact (Nat.pow_log_le_self 2 hApos.ne').trans hAle
  have hsub : k - (k - Nat.log 2 A) = Nat.log 2 A := by omega
  refine ⟨?_, ?_⟩
  · change 2 ^ (k - (k - Nat.log 2 A)) ≤ A
    rw [hsub]
    exact Nat.pow_log_le_self 2 hApos.ne'
  · change A < 2 ^ (k - (k - Nat.log 2 A) + 1)
    rw [hsub]
    exact Nat.lt_pow_succ_log_self (by norm_num) A

theorem blockIntegerLayerIndex_eq_of_mem
    {k v m : ℕ} {b : Fin v → ℕ} (hm : m ≤ k)
    (hb : b ∈ blockIntegerDyadicLayer k v m) :
    blockIntegerLayerIndex k b = m := by
  have hbData := mem_blockIntegerDyadicLayer.mp hb
  have hlog : Nat.log 2 (blockIntegerEnvelope k b) = k - m :=
    Nat.log_eq_of_pow_le_of_lt_pow hbData.2.1 hbData.2.2
  rw [blockIntegerLayerIndex, hlog]
  omega

theorem blockIntegerDyadicLayer_eq_indexFiber
    (k v m : ℕ) (hm : m ≤ k) :
    blockIntegerDyadicLayer k v m =
      (compositionsOf v k).filter fun b ↦ blockIntegerLayerIndex k b = m := by
  ext b
  simp only [Finset.mem_filter]
  constructor
  · intro hb
    exact ⟨(Finset.filter_subset _ _ hb),
      blockIntegerLayerIndex_eq_of_mem hm hb⟩
  · rintro ⟨hbComp, hindex⟩
    have hsum := mem_compositionsOf.mp hbComp
    have hlayer := mem_blockIntegerDyadicLayer_index hsum
    rwa [hindex] at hlayer

/-- The integral layer has the same closed Smirnov barrier as the real
half-open layer. -/
theorem blockIntegerDyadicLayer_subset_smirnov
    (k v m : ℕ) :
    blockIntegerDyadicLayer k v m ⊆
      smirnovOccupancies k (m + blockLayerSlack k) v := by
  intro b hb
  have hbData := mem_blockIntegerDyadicLayer.mp hb
  rw [mem_smirnovOccupancies]
  refine ⟨hbData.1, ?_⟩
  intro h hh hvh
  let C := blockPrefixCount b h
  let W := blockPrefixWeight b h
  have hCk : C ≤ k := blockPrefixCount_le_total b hbData.1 hvh
  have hlow : 2 ^ (k - m) ≤ blockIntegerPrefixEnvelope k b h :=
    hbData.2.1.trans (blockIntegerEnvelope_le_prefix k b hvh)
  have hpower : 2 ^ C ≤ 2 ^ m * (W + 1) := by
    by_cases hmk : m ≤ k
    · have hsplit : k = (k - m) + m := (Nat.sub_add_cancel hmk).symm
      have hkc : k = (k - C) + C := (Nat.sub_add_cancel hCk).symm
      dsimp [blockIntegerPrefixEnvelope] at hlow
      have hmul := Nat.mul_le_mul_right (2 ^ m) hlow
      have hlhs : 2 ^ (k - m) * 2 ^ m = 2 ^ k := by
        rw [← pow_add, ← hsplit]
      rw [hlhs] at hmul
      have hkcpow : 2 ^ k = 2 ^ (k - C) * 2 ^ C := by
        rw [← pow_add, ← hkc]
      rw [hkcpow] at hmul
      have hscaled : 2 ^ (k - C) * 2 ^ C ≤
          2 ^ (k - C) * (2 ^ m * (W + 1)) := by
        calc
          2 ^ (k - C) * 2 ^ C ≤
              (2 ^ (k - C) * (W + 1)) * 2 ^ m := hmul
          _ = 2 ^ (k - C) * (2 ^ m * (W + 1)) := by ring
      exact Nat.le_of_mul_le_mul_left hscaled (by positivity)
    · have hkm : k < m := lt_of_not_ge hmk
      have htrivial : 2 ^ C ≤ 2 ^ m :=
        Nat.pow_le_pow_right (by omega) (hCk.trans hkm.le)
      exact htrivial.trans (by
        calc
          2 ^ m = 2 ^ m * 1 := by ring
          _ ≤ 2 ^ m * (W + 1) :=
            Nat.mul_le_mul_left _ (by omega))
  have hW : W ≤ C * 2 ^ h := blockPrefixWeight_le_count_mul_pow b h
  have hWcoarse : W + 1 ≤ (k + 1) * 2 ^ h := by
    have hp : 1 ≤ 2 ^ h := one_le_pow₀ (by omega)
    have hmul : C * 2 ^ h ≤ k * 2 ^ h := Nat.mul_le_mul_right _ hCk
    calc
      W + 1 ≤ C * 2 ^ h + 1 := Nat.add_le_add_right hW 1
      _ ≤ k * 2 ^ h + 2 ^ h := Nat.add_le_add hmul hp
      _ = (k + 1) * 2 ^ h := by ring
  have hstrict : 2 ^ m * (W + 1) <
      2 ^ (m + h + blockLayerSlack k) := by
    calc
      2 ^ m * (W + 1) ≤ 2 ^ m * ((k + 1) * 2 ^ h) :=
        Nat.mul_le_mul_left _ hWcoarse
      _ = 2 ^ (m + h) * (k + 1) := by rw [pow_add]; ring
      _ < 2 ^ (m + h) * 2 ^ blockLayerSlack k :=
        Nat.mul_lt_mul_of_pos_left
          (add_one_lt_two_pow_blockLayerSlack k) (by positivity)
      _ = 2 ^ (m + h + blockLayerSlack k) := by rw [← pow_add]
  have hClt : C < m + h + blockLayerSlack k :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp (hpower.trans_lt hstrict)
  change blockPrefixCount b h < m + h + blockLayerSlack k at hClt
  rw [blockPrefixCount_eq_occupancyPrefix b hvh] at hClt
  omega

/-- Uniform cluster bound on an exact integral layer. -/
theorem blockIntegerDyadicLayer_clusterLength_le
    {M k v m : ℕ} {b : Fin v → ℕ}
    (hb : b ∈ blockIntegerDyadicLayer k v m)
    {a : ℕ} (ha : a ∈ compositionBlockFamily M b) :
    clusterLength a ≤
      sharpBlockLayerScale M * (2 : ℝ) ^ (k - m + 1) := by
  have hbData := mem_blockIntegerDyadicLayer.mp hb
  exact (compositionBlock_clusterLength_le_scaledIntegerEnvelope
      hbData.1 ha).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hbData.2.2.le)
      (sharpBlockLayerScale_pos M).le)

end Erdos446
