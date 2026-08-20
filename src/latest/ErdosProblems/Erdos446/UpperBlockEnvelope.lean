/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperBlockOccupancy

/-!
# Erdős Problem 446: a prime-block prefix envelope for cluster length

For a squarefree integer selected from consecutive prime blocks, choose the
prime factors in the first `h` blocks as the prefix in Ford's elementary
cluster inequality.  Their product is bounded by the `h`th block endpoint,
and the remaining number of prime factors is determined by the block-count
vector.  This gives a completely discrete version of the integrand in Ford's
order-statistics argument.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Number of selected primes in the first `h` blocks. -/
def blockPrefixCount {v : ℕ} (b : Fin v → ℕ) (h : ℕ) : ℕ :=
  ∑ i ∈ Finset.range h, extendComposition b i

/-- Endpoint-weighted number of primes in the first `h` blocks. -/
def blockPrefixWeight {v : ℕ} (b : Fin v → ℕ) (h : ℕ) : ℕ :=
  ∑ i ∈ Finset.range h, extendComposition b i * 2 ^ i

/-- The prefix envelope obtained by cutting after the first `h` blocks. -/
noncomputable def blockClusterPrefixEnvelope
    (M k : ℕ) {v : ℕ} (b : Fin v → ℕ) (h : ℕ) : ℝ :=
  (2 : ℝ) ^ (k - blockPrefixCount b h) *
    ((((blockPrefixCount b h : ℕ) : ℝ) * (2 : ℝ) ^ (M + h) + 1) *
      Real.log 2)

/-- Minimum of the valid prefix envelopes.  This is the discrete block
analogue of Ford's ordered-simplex integrand. -/
noncomputable def blockClusterEnvelope
    (M k : ℕ) {v : ℕ} (b : Fin v → ℕ) : ℝ :=
  ((Finset.range (v + 1)).image
    (blockClusterPrefixEnvelope M k b)).min' (by
      exact Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- The sharp prefix envelope, retaining the individual prime-block weights
instead of replacing all of them by the last endpoint. -/
noncomputable def blockClusterSharpPrefixEnvelope
    (M k : ℕ) {v : ℕ} (b : Fin v → ℕ) (h : ℕ) : ℝ :=
  (2 : ℝ) ^ (k - blockPrefixCount b h) *
    (((2 : ℝ) ^ (M + 1) * (blockPrefixWeight b h : ℝ) + 1) *
      Real.log 2)

/-- Minimum of the sharp prefix envelopes. -/
noncomputable def blockClusterSharpEnvelope
    (M k : ℕ) {v : ℕ} (b : Fin v → ℕ) : ℝ :=
  ((Finset.range (v + 1)).image
    (blockClusterSharpPrefixEnvelope M k b)).min' (by
      exact Finset.image_nonempty.mpr ⟨0, by simp⟩)

theorem blockClusterEnvelope_le_prefix
    (M k : ℕ) {v : ℕ} (b : Fin v → ℕ) {h : ℕ} (hh : h ≤ v) :
    blockClusterEnvelope M k b ≤ blockClusterPrefixEnvelope M k b h := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨h, Finset.mem_range.mpr (by omega), rfl⟩

theorem blockPrefixCount_eq_occupancyPrefix
    {v : ℕ} (b : Fin v → ℕ) {h : ℕ} (hh : h ≤ v) :
    blockPrefixCount b h = occupancyPrefix b h := by
  classical
  rw [blockPrefixCount, occupancyPrefix]
  apply Finset.sum_bij (fun i hi ↦ ⟨i, lt_of_lt_of_le (Finset.mem_range.mp hi) hh⟩)
  · intro i hi
    simp [Finset.mem_range.mp hi]
  · intro i₁ hi₁ i₂ hi₂ heq
    simpa using congrArg Fin.val heq
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨i.val, Finset.mem_range.mpr hi, ?_⟩
    exact Fin.ext rfl
  · intro i hi
    simp only [extendComposition]
    rw [dif_pos (lt_of_lt_of_le (Finset.mem_range.mp hi) hh)]

private theorem prefixSelection_card
    {M v : ℕ} {b : Fin v → ℕ} {S : Finset ℕ}
    (hS : S ∈ blockSelectionSets M v (extendComposition b))
    {h : ℕ} (hh : h ≤ v) :
    (S ∩ blockPool M h).card = blockPrefixCount b h := by
  let J := S ∩ blockPool M h
  have hJ : J = (Finset.range h).biUnion fun i ↦
      J ∩ primeBlock (M + i) := by
    exact selection_eq_biUnion_blocks Finset.inter_subset_right
  change J.card = blockPrefixCount b h
  rw [hJ, Finset.card_biUnion (block_inter_pairwiseDisjoint M h J)]
  apply Finset.sum_congr rfl
  intro i hi
  have hiv : i < v := (Finset.mem_range.mp hi).trans_le hh
  have hblockSubset : primeBlock (M + i) ⊆ blockPool M h := by
    intro p hp
    exact mem_blockPool.mpr ⟨i, Finset.mem_range.mp hi, hp⟩
  have hinter : J ∩ primeBlock (M + i) =
      S ∩ primeBlock (M + i) := by
    ext p
    simp only [J, Finset.mem_inter]
    constructor
    · rintro ⟨⟨hpS, hpPool⟩, hpBlock⟩
      exact ⟨hpS, hpBlock⟩
    · rintro ⟨hpS, hpBlock⟩
      exact ⟨⟨hpS, hblockSubset hpBlock⟩, hpBlock⟩
  rw [hinter, (mem_blockSelectionSets.mp hS).2 i hiv]

private theorem mem_prefixSelection_le_endpoint
    {M h p : ℕ} (hp : p ∈ blockPool M h) :
    p ≤ blockEndpoint (M + h) := by
  obtain ⟨i, hi, hpBlock⟩ := mem_blockPool.mp hp
  have hpUpper := (mem_primeBlock.mp hpBlock).2.2
  exact hpUpper.trans (blockEndpoint_mono (by omega))

private theorem log_prefixSelection_le
    {M h : ℕ} (S : Finset ℕ) :
    Real.log (((S ∩ blockPool M h).prod id : ℕ) : ℝ) ≤
      ((S ∩ blockPool M h).card : ℝ) *
        ((2 : ℝ) ^ (M + h) * Real.log 2) := by
  let J := S ∩ blockPool M h
  change Real.log (((J.prod id : ℕ) : ℝ)) ≤
    (J.card : ℝ) * ((2 : ℝ) ^ (M + h) * Real.log 2)
  have hprodPos : 0 < J.prod id := by
    apply Finset.prod_pos
    intro p hp
    have hpPool := (Finset.mem_inter.mp hp).2
    exact (prime_of_mem_blockPool hpPool).pos
  have hprodLe : J.prod id ≤ blockEndpoint (M + h) ^ J.card := by
    exact Finset.prod_le_pow_card J id (blockEndpoint (M + h))
      (fun p hp ↦ mem_prefixSelection_le_endpoint
        (Finset.mem_inter.mp hp).2)
  have hprodPosR : (0 : ℝ) < ((J.prod id : ℕ) : ℝ) := by
    exact_mod_cast hprodPos
  have hprodLeR : ((J.prod id : ℕ) : ℝ) ≤
      (((blockEndpoint (M + h) ^ J.card : ℕ) : ℝ)) := by
    exact_mod_cast hprodLe
  have hlog := Real.log_le_log hprodPosR hprodLeR
  rw [Nat.cast_pow, Real.log_pow, log_blockEndpoint] at hlog
  simpa only [J, Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul] using hlog

private theorem log_prefixSelection_le_weight
    {M v : ℕ} {b : Fin v → ℕ} {S : Finset ℕ}
    (hS : S ∈ blockSelectionSets M v (extendComposition b))
    {h : ℕ} (hh : h ≤ v) :
    Real.log (((S ∩ blockPool M h).prod id : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (M + 1) * (blockPrefixWeight b h : ℝ) * Real.log 2 := by
  let J := S ∩ blockPool M h
  have hJ : J = (Finset.range h).biUnion fun i ↦
      J ∩ primeBlock (M + i) :=
    selection_eq_biUnion_blocks Finset.inter_subset_right
  have hlogProd :
      Real.log (((J.prod id : ℕ) : ℝ)) = ∑ p ∈ J, Real.log (p : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    simp only [id_eq]
    intro p hp
    have hpPool := (Finset.mem_inter.mp hp).2
    exact_mod_cast (prime_of_mem_blockPool hpPool).ne_zero
  rw [show S ∩ blockPool M h = J by rfl, hlogProd, hJ,
    Finset.sum_biUnion (block_inter_pairwiseDisjoint M h J)]
  calc
    (∑ i ∈ Finset.range h,
        ∑ p ∈ J ∩ primeBlock (M + i), Real.log (p : ℝ)) ≤
        ∑ i ∈ Finset.range h,
          (extendComposition b i : ℝ) *
            ((2 : ℝ) ^ (M + i + 1) * Real.log 2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiv : i < v := (Finset.mem_range.mp hi).trans_le hh
      have hblockSubset : primeBlock (M + i) ⊆ blockPool M h := by
        intro p hp
        exact mem_blockPool.mpr ⟨i, Finset.mem_range.mp hi, hp⟩
      have hinter : J ∩ primeBlock (M + i) =
          S ∩ primeBlock (M + i) := by
        ext p
        simp only [J, Finset.mem_inter]
        constructor
        · rintro ⟨⟨hpS, hpPool⟩, hpBlock⟩
          exact ⟨hpS, hpBlock⟩
        · rintro ⟨hpS, hpBlock⟩
          exact ⟨⟨hpS, hblockSubset hpBlock⟩, hpBlock⟩
      have hcard : (J ∩ primeBlock (M + i)).card = extendComposition b i := by
        rw [hinter, (mem_blockSelectionSets.mp hS).2 i hiv]
      calc
        (∑ p ∈ J ∩ primeBlock (M + i), Real.log (p : ℝ)) ≤
            ∑ _p ∈ J ∩ primeBlock (M + i),
              ((2 : ℝ) ^ (M + i + 1) * Real.log 2) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpBlock := (Finset.mem_inter.mp hp).2
          have hpData := mem_primeBlock.mp hpBlock
          have hpPosR : (0 : ℝ) < p := by exact_mod_cast hpData.1.pos
          have hpLeR : (p : ℝ) ≤ blockEndpoint (M + i + 1) := by
            exact_mod_cast hpData.2.2
          have := Real.log_le_log hpPosR hpLeR
          simpa only [log_blockEndpoint] using this
        _ = (extendComposition b i : ℝ) *
            ((2 : ℝ) ^ (M + i + 1) * Real.log 2) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ = (2 : ℝ) ^ (M + 1) * (blockPrefixWeight b h : ℝ) *
        Real.log 2 := by
      rw [blockPrefixWeight]
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show M + i + 1 = (M + 1) + i by omega, pow_add]
      ring

/-- Every prefix of a block-count vector supplies a valid cluster-length
envelope. -/
theorem compositionBlock_clusterLength_le_prefixEnvelope
    {M k v : ℕ} {b : Fin v → ℕ}
    (hb : ∑ i : Fin v, b i = k) {a : ℕ}
    (ha : a ∈ compositionBlockFamily M b)
    {h : ℕ} (hh : h ≤ v) :
    clusterLength a ≤ blockClusterPrefixEnvelope M k b h := by
  obtain ⟨S, hS, rfl⟩ := mem_blockFamily.mp ha
  let J := S ∩ blockPool M h
  have hJsub : J ⊆ S := Finset.inter_subset_left
  have hprimeFactors := selectionProduct_primeFactors hS
  have hJsupport : J ⊆ (S.prod id).primeFactors := by
    simpa only [hprimeFactors] using hJsub
  have hsq : Squarefree (S.prod id) := selectionProduct_squarefree hS
  have hSCard : S.card = k := by
    rw [card_selection_eq_sum hS, sum_range_extendComposition, hb]
  have hJCard : J.card = blockPrefixCount b h := by
    exact prefixSelection_card hS hh
  have hdiffCard : ((S.prod id).primeFactors \ J).card =
      k - blockPrefixCount b h := by
    rw [hprimeFactors, Finset.card_sdiff_of_subset hJsub, hSCard, hJCard]
  have hcluster := clusterLength_squarefree_prefix hsq hJsupport
  have hlog := log_prefixSelection_le (M := M) (h := h) S
  change clusterLength (S.prod id) ≤
      (2 : ℝ) ^ ((S.prod id).primeFactors \ J).card *
        (Real.log ((J.prod id : ℕ) : ℝ) + Real.log 2) at hcluster
  rw [hdiffCard] at hcluster
  rw [blockClusterPrefixEnvelope]
  have hpow : 0 ≤ (2 : ℝ) ^ (k - blockPrefixCount b h) := by positivity
  apply hcluster.trans
  apply mul_le_mul_of_nonneg_left _ hpow
  rw [hJCard] at hlog
  nlinarith [Real.log_nonneg one_le_two]

/-- Taking the best prefix gives the exact finite cluster envelope used by
the subsequent occupancy-layer argument. -/
theorem compositionBlock_clusterLength_le_envelope
    {M k v : ℕ} {b : Fin v → ℕ}
    (hb : ∑ i : Fin v, b i = k) {a : ℕ}
    (ha : a ∈ compositionBlockFamily M b) :
    clusterLength a ≤ blockClusterEnvelope M k b := by
  rw [blockClusterEnvelope]
  apply Finset.le_min'
  intro x hx
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
  exact compositionBlock_clusterLength_le_prefixEnvelope hb ha
    (Nat.le_of_lt_succ (Finset.mem_range.mp hh))

/-- Pointwise sharp prefix estimate. -/
theorem compositionBlock_clusterLength_le_sharpPrefixEnvelope
    {M k v : ℕ} {b : Fin v → ℕ}
    (hb : ∑ i : Fin v, b i = k) {a : ℕ}
    (ha : a ∈ compositionBlockFamily M b)
    {h : ℕ} (hh : h ≤ v) :
    clusterLength a ≤ blockClusterSharpPrefixEnvelope M k b h := by
  obtain ⟨S, hS, rfl⟩ := mem_blockFamily.mp ha
  let J := S ∩ blockPool M h
  have hJsub : J ⊆ S := Finset.inter_subset_left
  have hprimeFactors := selectionProduct_primeFactors hS
  have hJsupport : J ⊆ (S.prod id).primeFactors := by
    simpa only [hprimeFactors] using hJsub
  have hsq : Squarefree (S.prod id) := selectionProduct_squarefree hS
  have hSCard : S.card = k := by
    rw [card_selection_eq_sum hS, sum_range_extendComposition, hb]
  have hJCard : J.card = blockPrefixCount b h := prefixSelection_card hS hh
  have hdiffCard : ((S.prod id).primeFactors \ J).card =
      k - blockPrefixCount b h := by
    rw [hprimeFactors, Finset.card_sdiff_of_subset hJsub, hSCard, hJCard]
  have hcluster := clusterLength_squarefree_prefix hsq hJsupport
  have hlog := log_prefixSelection_le_weight hS hh
  change clusterLength (S.prod id) ≤
      (2 : ℝ) ^ ((S.prod id).primeFactors \ J).card *
        (Real.log ((J.prod id : ℕ) : ℝ) + Real.log 2) at hcluster
  rw [hdiffCard] at hcluster
  rw [blockClusterSharpPrefixEnvelope]
  have hpow : 0 ≤ (2 : ℝ) ^ (k - blockPrefixCount b h) := by positivity
  apply hcluster.trans
  apply mul_le_mul_of_nonneg_left _ hpow
  nlinarith [Real.log_nonneg one_le_two]

/-- The best sharp prefix controls every member of the block family. -/
theorem compositionBlock_clusterLength_le_sharpEnvelope
    {M k v : ℕ} {b : Fin v → ℕ}
    (hb : ∑ i : Fin v, b i = k) {a : ℕ}
    (ha : a ∈ compositionBlockFamily M b) :
    clusterLength a ≤ blockClusterSharpEnvelope M k b := by
  rw [blockClusterSharpEnvelope]
  apply Finset.le_min'
  intro x hx
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
  exact compositionBlock_clusterLength_le_sharpPrefixEnvelope hb ha
    (Nat.le_of_lt_succ (Finset.mem_range.mp hh))

end Erdos446
