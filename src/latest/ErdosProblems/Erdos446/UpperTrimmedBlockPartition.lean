/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperResidualPrimeEuler
import ErdosProblems.Erdos446.UpperDepthPartition

/-!
# Erdős Problem 446: the retained/residual block partition

This file performs the support-side bookkeeping after the one-sided trimming
of every reciprocal-prime block.  The residual primes are adjoined to the
fixed small-prime pool, while the retained primes remain separated by their
original Ford blocks.  The two pools are disjoint and cover every prime in
the original small/block partition.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable section

/-- The retained primes in blocks `M, ..., M + K - 1`. -/
def retainedPrimePool (M K : ℕ) : Finset ℕ :=
  (Finset.range K).biUnion (fun i ↦ retainedPrimeBlock (M + i))

/-- The fixed small primes together with all residual primes in the finite
block window. -/
def trimmedAuxiliaryPrimePool (M K : ℕ) : Finset ℕ :=
  smallPrimePool M ∪ residualPrimePool M K

theorem retainedPrimePool_subset_blockPool (M K : ℕ) :
    retainedPrimePool M K ⊆ blockPool M K := by
  intro p hp
  obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
  exact mem_blockPool.mpr
    ⟨i, Finset.mem_range.mp hi, retainedPrimeBlock_subset (M + i) hp⟩

theorem residualPrimePool_subset_blockPool (M K : ℕ) :
    residualPrimePool M K ⊆ blockPool M K := by
  intro p hp
  obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
  exact mem_blockPool.mpr
    ⟨i, Finset.mem_range.mp hi, residualPrimeBlock_subset (M + i) hp⟩

theorem retainedPrimePool_union_residualPrimePool (M K : ℕ) :
    retainedPrimePool M K ∪ residualPrimePool M K = blockPool M K := by
  ext p
  simp only [retainedPrimePool, residualPrimePool, blockPool,
    Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro (⟨i, hi, hp⟩ | ⟨i, hi, hp⟩)
    · exact ⟨i, hi, retainedPrimeBlock_subset (M + i) hp⟩
    · exact ⟨i, hi, residualPrimeBlock_subset (M + i) hp⟩
  · rintro ⟨i, hi, hp⟩
    rw [← retainedPrimeBlock_union_residual (M + i)] at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Or.inl ⟨i, hi, hp⟩
    · exact Or.inr ⟨i, hi, hp⟩

theorem retainedPrimePool_disjoint_residualPrimePool (M K : ℕ) :
    Disjoint (retainedPrimePool M K) (residualPrimePool M K) := by
  rw [Finset.disjoint_left]
  intro p hpRet hpRes
  obtain ⟨i, hi, hpI⟩ := Finset.mem_biUnion.mp hpRet
  obtain ⟨j, hj, hpJ⟩ := Finset.mem_biUnion.mp hpRes
  by_cases hij : i = j
  · subst j
    exact (Finset.disjoint_left.mp
      (retainedPrimeBlock_disjoint_residual (M + i))) hpI hpJ
  · exact (Finset.disjoint_left.mp
      (primeBlock_pairwise_disjoint (i := M + i) (j := M + j) (by omega)))
        (retainedPrimeBlock_subset (M + i) hpI)
        (residualPrimeBlock_subset (M + j) hpJ)

theorem smallPrimePool_disjoint_retainedPrimePool (M K : ℕ) :
    Disjoint (smallPrimePool M) (retainedPrimePool M K) :=
  Finset.disjoint_of_subset_right (retainedPrimePool_subset_blockPool M K)
    (smallPrimePool_disjoint_blockPool M K)

theorem trimmedAuxiliaryPrimePool_disjoint_retainedPrimePool (M K : ℕ) :
    Disjoint (trimmedAuxiliaryPrimePool M K) (retainedPrimePool M K) := by
  rw [trimmedAuxiliaryPrimePool, Finset.disjoint_union_left]
  exact ⟨smallPrimePool_disjoint_retainedPrimePool M K,
    (retainedPrimePool_disjoint_residualPrimePool M K).symm⟩

theorem trimmedAuxiliaryPrimePool_union_retainedPrimePool (M K : ℕ) :
    trimmedAuxiliaryPrimePool M K ∪ retainedPrimePool M K =
      smallPrimePool M ∪ blockPool M K := by
  rw [trimmedAuxiliaryPrimePool, ← retainedPrimePool_union_residualPrimePool]
  ext p
  simp only [Finset.mem_union]
  tauto

theorem primesUpTo_endpoint_eq_trimmed_union_retained (M K : ℕ) :
    primesUpTo (blockEndpoint (M + K)) =
      trimmedAuxiliaryPrimePool M K ∪ retainedPrimePool M K := by
  rw [smoothSupport_eq_small_union_blocks,
    trimmedAuxiliaryPrimePool_union_retainedPrimePool]

/-- Cardinality vector of a subset of the retained pool. -/
def retainedBlockCountVector (M : ℕ) {K : ℕ}
    (S : Finset ℕ) : Fin K → ℕ :=
  fun i ↦ (S ∩ retainedPrimeBlock (M + i)).card

/-- Retained supports with prescribed block cardinalities. -/
def retainedBlockSelectionSets (M K : ℕ) (b : Fin K → ℕ) :
    Finset (Finset ℕ) :=
  (retainedPrimePool M K).powerset.filter fun S ↦
    retainedBlockCountVector M S = b

theorem mem_retainedBlockSelectionSets
    {M K : ℕ} {b : Fin K → ℕ} {S : Finset ℕ} :
    S ∈ retainedBlockSelectionSets M K b ↔
      S ⊆ retainedPrimePool M K ∧ retainedBlockCountVector M S = b := by
  simp [retainedBlockSelectionSets]

theorem retainedBlockSelectionSets_subset_original
    {M K : ℕ} {b : Fin K → ℕ} {S : Finset ℕ}
    (hS : S ∈ retainedBlockSelectionSets M K b) :
    S ∈ blockSelectionSets M K (extendComposition b) := by
  rw [mem_blockSelectionSets]
  refine ⟨(mem_retainedBlockSelectionSets.mp hS).1.trans
    (retainedPrimePool_subset_blockPool M K), ?_⟩
  intro i hi
  let ii : Fin K := ⟨i, hi⟩
  have hb := congrFun (mem_retainedBlockSelectionSets.mp hS).2 ii
  rw [extendComposition, dif_pos hi]
  rw [retainedBlockCountVector] at hb
  have hsub : S ∩ primeBlock (M + i) =
      S ∩ retainedPrimeBlock (M + i) := by
    ext p
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hpS, hpBlock⟩
      have hpPool := (mem_retainedBlockSelectionSets.mp hS).1 hpS
      obtain ⟨j, hj, hpRet⟩ := Finset.mem_biUnion.mp hpPool
      have hji : j = i := by
        by_contra hne
        exact (Finset.disjoint_left.mp
          (primeBlock_pairwise_disjoint (i := M + j) (j := M + i) (by omega)))
            (retainedPrimeBlock_subset (M + j) hpRet) hpBlock
      subst j
      exact ⟨hpS, hpRet⟩
    · rintro ⟨hpS, hpRet⟩
      exact ⟨hpS, retainedPrimeBlock_subset (M + i) hpRet⟩
  rw [hsub]
  exact hb

theorem card_retainedSelection_eq_sum
    {M K : ℕ} {b : Fin K → ℕ} {S : Finset ℕ}
    (hS : S ∈ retainedBlockSelectionSets M K b) :
    S.card = ∑ i : Fin K, b i := by
  have hOriginal := retainedBlockSelectionSets_subset_original hS
  rw [card_selection_eq_sum hOriginal]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [extendComposition_fin]

theorem retainedBlockSelectionSets_pairwiseDisjoint
    (M K k : ℕ) :
    ((compositionsOf K k : Finset (Fin K → ℕ)) : Set (Fin K → ℕ)).PairwiseDisjoint
      (retainedBlockSelectionSets M K) := by
  intro b hb c hc hbc
  change Disjoint (retainedBlockSelectionSets M K b)
    (retainedBlockSelectionSets M K c)
  rw [Finset.disjoint_left]
  intro S hSb hSc
  have hb' := (mem_retainedBlockSelectionSets.mp hSb).2
  have hc' := (mem_retainedBlockSelectionSets.mp hSc).2
  exact hbc (hb'.symm.trans hc')

/-- Exact fixed-cardinality partition of the retained supports by their
block-count composition. -/
theorem retainedBlockSelectionSets_disjiUnion
    (M K k : ℕ) :
    (compositionsOf K k).disjiUnion
        (retainedBlockSelectionSets M K)
        (retainedBlockSelectionSets_pairwiseDisjoint M K k) =
      (retainedPrimePool M K).powersetCard k := by
  ext S
  simp only [Finset.mem_disjiUnion, Finset.mem_powersetCard]
  constructor
  · rintro ⟨b, hb, hS⟩
    have hmem := mem_retainedBlockSelectionSets.mp hS
    exact ⟨hmem.1, by
      rw [card_retainedSelection_eq_sum hS]
      exact mem_compositionsOf.mp hb⟩
  · rintro ⟨hSsub, hScard⟩
    let b : Fin K → ℕ := retainedBlockCountVector M S
    have hSel : S ∈ retainedBlockSelectionSets M K b :=
      mem_retainedBlockSelectionSets.mpr ⟨hSsub, rfl⟩
    refine ⟨b, mem_compositionsOf.mpr ?_, hSel⟩
    rw [← card_retainedSelection_eq_sum hSel, hScard]

end

end Erdos446
