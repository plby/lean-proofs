/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.PrimeBlocks

/-!
# Erdős Problem 446: squarefree prime-block families

This file packages Ford's vector class `A(b)`.  Its elements are products of
prime subsets having prescribed cardinality in each of a consecutive list of
reciprocal-prime blocks.  The product map is injective, because its prime
factors recover the selected subset.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- The union of `k` consecutive prime blocks beginning with block `M`. -/
def blockPool (M k : ℕ) : Finset ℕ :=
  (Finset.range k).biUnion fun i ↦ primeBlock (M + i)

/-- Prime subsets with vector of block cardinalities `b`. -/
def blockSelectionSets (M k : ℕ) (b : ℕ → ℕ) : Finset (Finset ℕ) :=
  (blockPool M k).powerset.filter fun S ↦
    ∀ i ∈ Finset.range k, (S ∩ primeBlock (M + i)).card = b i

/-- The corresponding family of squarefree integers. -/
def blockFamily (M k : ℕ) (b : ℕ → ℕ) : Finset ℕ :=
  (blockSelectionSets M k b).image fun S ↦ S.prod id

/-- Reciprocal weight of one selected prime set. -/
noncomputable def selectionWeight (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, 1 / (p : ℝ)

/-- Independent choices of one prescribed-cardinality prime subset in every
block. -/
def blockChoiceTuples (M k : ℕ) (b : ℕ → ℕ) :
    Finset (Fin k → Finset ℕ) :=
  Fintype.piFinset fun i : Fin k ↦
    (primeBlock (M + i)).powersetCard (b i)

/-- Union of all coordinate choices.  The coordinates lie in disjoint prime
blocks. -/
def choiceUnion {k : ℕ} (T : Fin k → Finset ℕ) : Finset ℕ :=
  Finset.univ.biUnion T

/-- The `r`th elementary reciprocal-prime sum in block `j`. -/
noncomputable def blockElementaryMass (j r : ℕ) : ℝ :=
  ∑ S ∈ (primeBlock j).powersetCard r, selectionWeight S

theorem mem_blockPool {M k p : ℕ} :
    p ∈ blockPool M k ↔ ∃ i < k, p ∈ primeBlock (M + i) := by
  simp [blockPool]

theorem prime_of_mem_blockPool {M k p : ℕ} (hp : p ∈ blockPool M k) :
    p.Prime := by
  obtain ⟨i, hi, hp⟩ := mem_blockPool.mp hp
  exact (mem_primeBlock.mp hp).1

theorem mem_blockSelectionSets {M k : ℕ} {b : ℕ → ℕ} {S : Finset ℕ} :
    S ∈ blockSelectionSets M k b ↔
      S ⊆ blockPool M k ∧
        ∀ i < k, (S ∩ primeBlock (M + i)).card = b i := by
  simp only [blockSelectionSets, Finset.mem_filter, Finset.mem_powerset,
    Finset.mem_range]

theorem prime_of_mem_selection {M k : ℕ} {b : ℕ → ℕ}
    {S : Finset ℕ} (hS : S ∈ blockSelectionSets M k b) {p : ℕ}
    (hp : p ∈ S) : p.Prime :=
  prime_of_mem_blockPool ((mem_blockSelectionSets.mp hS).1 hp)

theorem mem_blockChoiceTuples {M k : ℕ} {b : ℕ → ℕ}
    {T : Fin k → Finset ℕ} :
    T ∈ blockChoiceTuples M k b ↔
      ∀ i : Fin k, T i ⊆ primeBlock (M + i) ∧ (T i).card = b i := by
  simp [blockChoiceTuples, Finset.mem_powersetCard]

theorem blockChoice_pairwiseDisjoint {M k : ℕ} {b : ℕ → ℕ}
    {T : Fin k → Finset ℕ} (hT : T ∈ blockChoiceTuples M k b) :
    ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint T := by
  intro i hi j hj hij
  exact Finset.disjoint_of_subset_right (mem_blockChoiceTuples.mp hT j).1
    (Finset.disjoint_of_subset_left (mem_blockChoiceTuples.mp hT i).1
      (primeBlock_pairwise_disjoint (by
        intro h
        apply hij
        apply Fin.ext
        omega)))

theorem choiceUnion_inter_block {M k : ℕ} {b : ℕ → ℕ}
    {T : Fin k → Finset ℕ} (hT : T ∈ blockChoiceTuples M k b)
    (i : Fin k) :
    choiceUnion T ∩ primeBlock (M + i) = T i := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpU, hpBlock⟩ := Finset.mem_inter.mp hp
    obtain ⟨j, hj, hpTj⟩ := Finset.mem_biUnion.mp hpU
    have hji : j = i := by
      by_contra hne
      have hdisj := primeBlock_pairwise_disjoint (i := M + j) (j := M + i)
        (by omega)
      exact (Finset.disjoint_left.mp hdisj)
        ((mem_blockChoiceTuples.mp hT j).1 hpTj) hpBlock
    simpa [hji] using hpTj
  · intro hp
    exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, hp⟩, (mem_blockChoiceTuples.mp hT i).1 hp⟩

theorem choiceUnion_mem_blockSelectionSets {M k : ℕ} {b : ℕ → ℕ}
    {T : Fin k → Finset ℕ} (hT : T ∈ blockChoiceTuples M k b) :
    choiceUnion T ∈ blockSelectionSets M k b := by
  rw [mem_blockSelectionSets]
  constructor
  · intro p hp
    obtain ⟨i, hi, hpTi⟩ := Finset.mem_biUnion.mp hp
    apply mem_blockPool.mpr
    exact ⟨i, i.isLt,
      (mem_blockChoiceTuples.mp hT i).1 hpTi⟩
  · intro i hi
    let ii : Fin k := ⟨i, hi⟩
    rw [choiceUnion_inter_block hT ii]
    exact (mem_blockChoiceTuples.mp hT ii).2

theorem choiceUnion_injOn (M k : ℕ) (b : ℕ → ℕ) :
    Set.InjOn (choiceUnion (k := k)) (blockChoiceTuples M k b) := by
  intro T hT U hU hEq
  funext i
  rw [← choiceUnion_inter_block hT i,
    ← choiceUnion_inter_block hU i, hEq]

theorem image_choiceUnion_eq_blockSelectionSets (M k : ℕ) (b : ℕ → ℕ) :
    (blockChoiceTuples M k b).image choiceUnion =
      blockSelectionSets M k b := by
  ext S
  constructor
  · intro hS
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    exact choiceUnion_mem_blockSelectionSets hT
  · intro hS
    let T : Fin k → Finset ℕ := fun i ↦ S ∩ primeBlock (M + i)
    have hT : T ∈ blockChoiceTuples M k b := by
      rw [mem_blockChoiceTuples]
      intro i
      constructor
      · exact Finset.inter_subset_right
      · exact (mem_blockSelectionSets.mp hS).2 i i.isLt
    refine Finset.mem_image.mpr ⟨T, hT, ?_⟩
    apply Finset.ext
    intro p
    constructor
    · intro hp
      obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
      exact (Finset.mem_inter.mp hp).1
    · intro hp
      have hpPool := (mem_blockSelectionSets.mp hS).1 hp
      obtain ⟨i, hi, hpi⟩ := mem_blockPool.mp hpPool
      exact Finset.mem_biUnion.mpr
        ⟨⟨i, hi⟩, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hp, hpi⟩⟩

theorem selectionWeight_choiceUnion {M k : ℕ} {b : ℕ → ℕ}
    {T : Fin k → Finset ℕ} (hT : T ∈ blockChoiceTuples M k b) :
    selectionWeight (choiceUnion T) = ∏ i : Fin k, selectionWeight (T i) := by
  rw [selectionWeight, choiceUnion,
    Finset.prod_biUnion (blockChoice_pairwiseDisjoint hT)]
  rfl

theorem block_inter_pairwiseDisjoint (M k : ℕ) (S : Finset ℕ) :
    ((Finset.range k : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun i ↦ S ∩ primeBlock (M + i)) := by
  intro i hi j hj hij
  exact Finset.disjoint_of_subset_right (Finset.inter_subset_right)
    (Finset.disjoint_of_subset_left (Finset.inter_subset_right)
      (primeBlock_pairwise_disjoint (by omega)))

theorem selection_eq_biUnion_blocks {M k : ℕ} {S : Finset ℕ}
    (hS : S ⊆ blockPool M k) :
    S = (Finset.range k).biUnion fun i ↦ S ∩ primeBlock (M + i) := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi, hpi⟩ := mem_blockPool.mp (hS hp)
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_range.mpr hi, Finset.mem_inter.mpr ⟨hp, hpi⟩⟩
  · intro hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_inter.mp hp).1

theorem card_selection_eq_sum {M k : ℕ} {b : ℕ → ℕ}
    {S : Finset ℕ} (hS : S ∈ blockSelectionSets M k b) :
    S.card = ∑ i ∈ Finset.range k, b i := by
  have hmem := mem_blockSelectionSets.mp hS
  rw [selection_eq_biUnion_blocks hmem.1,
    Finset.card_biUnion (block_inter_pairwiseDisjoint M k S)]
  exact Finset.sum_congr rfl fun i hi ↦ hmem.2 i (Finset.mem_range.mp hi)

theorem selectionProduct_primeFactors {M k : ℕ} {b : ℕ → ℕ}
    {S : Finset ℕ} (hS : S ∈ blockSelectionSets M k b) :
    (S.prod id).primeFactors = S := by
  exact Nat.primeFactors_prod fun p hp ↦ prime_of_mem_selection hS hp

theorem selectionProduct_injOn (M k : ℕ) (b : ℕ → ℕ) :
    Set.InjOn (fun S : Finset ℕ ↦ S.prod id) (blockSelectionSets M k b) := by
  intro S hS T hT hprod
  rw [← selectionProduct_primeFactors hS,
    ← selectionProduct_primeFactors hT]
  exact congrArg Nat.primeFactors hprod

theorem selectionProduct_pos {M k : ℕ} {b : ℕ → ℕ}
    {S : Finset ℕ} (hS : S ∈ blockSelectionSets M k b) :
    0 < S.prod id := by
  apply Finset.prod_pos
  intro p hp
  exact (prime_of_mem_selection hS hp).pos

theorem selectionProduct_squarefree {M k : ℕ} {b : ℕ → ℕ}
    {S : Finset ℕ} (hS : S ∈ blockSelectionSets M k b) :
    Squarefree (S.prod id) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_
    (fun p hp ↦ (prime_of_mem_selection hS hp).squarefree)
  intro p hp q hq hpq
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes
    (prime_of_mem_selection hS hp)
    (prime_of_mem_selection hS hq)).mpr hpq

theorem mem_blockFamily {M k a : ℕ} {b : ℕ → ℕ} :
    a ∈ blockFamily M k b ↔
      ∃ S ∈ blockSelectionSets M k b, S.prod id = a := by
  simp [blockFamily]

theorem blockFamily_pos {M k : ℕ} {b : ℕ → ℕ} {a : ℕ}
    (ha : a ∈ blockFamily M k b) : 0 < a := by
  obtain ⟨S, hS, rfl⟩ := mem_blockFamily.mp ha
  exact selectionProduct_pos hS

theorem blockFamily_squarefree {M k : ℕ} {b : ℕ → ℕ} {a : ℕ}
    (ha : a ∈ blockFamily M k b) : Squarefree a := by
  obtain ⟨S, hS, rfl⟩ := mem_blockFamily.mp ha
  exact selectionProduct_squarefree hS

theorem selectionWeight_eq_inv_product (S : Finset ℕ) :
    selectionWeight S = 1 / ((S.prod id : ℕ) : ℝ) := by
  rw [selectionWeight]
  simp_rw [one_div]
  rw [Finset.prod_inv_distrib, Nat.cast_prod]
  simp

theorem blockSelection_weight_factorization (M k : ℕ) (b : ℕ → ℕ) :
    (∑ S ∈ blockSelectionSets M k b, selectionWeight S) =
      ∏ i : Fin k, blockElementaryMass (M + i) (b i) := by
  rw [← image_choiceUnion_eq_blockSelectionSets M k b,
    Finset.sum_image (choiceUnion_injOn M k b)]
  calc
    (∑ T ∈ blockChoiceTuples M k b, selectionWeight (choiceUnion T)) =
        ∑ T ∈ blockChoiceTuples M k b,
          ∏ i : Fin k, selectionWeight (T i) := by
      apply Finset.sum_congr rfl
      intro T hT
      exact selectionWeight_choiceUnion hT
    _ = ∏ i : Fin k, blockElementaryMass (M + i) (b i) := by
      rw [blockChoiceTuples]
      simp only [blockElementaryMass]
      rw [← Finset.prod_univ_sum]

theorem blockFamily_reciprocal_sum (M k : ℕ) (b : ℕ → ℕ) :
    (∑ a ∈ blockFamily M k b, 1 / (a : ℝ)) =
      ∑ S ∈ blockSelectionSets M k b, selectionWeight S := by
  rw [blockFamily, Finset.sum_image (selectionProduct_injOn M k b)]
  apply Finset.sum_congr rfl
  intro S hS
  exact (selectionWeight_eq_inv_product S).symm

theorem blockFamily_reciprocal_sum_factorization
    (M k : ℕ) (b : ℕ → ℕ) :
    (∑ a ∈ blockFamily M k b, 1 / (a : ℝ)) =
      ∏ i : Fin k, blockElementaryMass (M + i) (b i) := by
  rw [blockFamily_reciprocal_sum, blockSelection_weight_factorization]

end Erdos446
