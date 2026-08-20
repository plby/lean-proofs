/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperTrimmedBlockPartition
import ErdosProblems.Erdos446.UpperWeightedLayerNumericalFinal

/-!
# Erdős Problem 446: sharp mass of the retained blocks

The retained subblock in every Ford cell has reciprocal mass at most
`log 2`.  This module repeats the finite independent-choice factorization
for those subblocks and then applies the closed exceptional-layer estimate.
Unlike the untrimmed comparison, no offset condition involving `2^M` is
needed.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable section

/-- Independent choices from the retained part of each block. -/
def retainedBlockChoiceTuples (M K : ℕ) (b : Fin K → ℕ) :
    Finset (Fin K → Finset ℕ) :=
  Fintype.piFinset fun i : Fin K ↦
    (retainedPrimeBlock (M + i)).powersetCard (b i)

theorem mem_retainedBlockChoiceTuples
    {M K : ℕ} {b : Fin K → ℕ} {T : Fin K → Finset ℕ} :
    T ∈ retainedBlockChoiceTuples M K b ↔
      ∀ i : Fin K,
        T i ⊆ retainedPrimeBlock (M + i) ∧ (T i).card = b i := by
  simp [retainedBlockChoiceTuples, Finset.mem_powersetCard]

theorem retainedBlockChoice_pairwiseDisjoint
    {M K : ℕ} {b : Fin K → ℕ} {T : Fin K → Finset ℕ}
    (hT : T ∈ retainedBlockChoiceTuples M K b) :
    ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint T := by
  intro i hi j hj hij
  exact Finset.disjoint_of_subset_right
    (mem_retainedBlockChoiceTuples.mp hT j).1
    (Finset.disjoint_of_subset_left
      (mem_retainedBlockChoiceTuples.mp hT i).1
      (Disjoint.mono (retainedPrimeBlock_subset (M + i))
        (retainedPrimeBlock_subset (M + j))
        (primeBlock_pairwise_disjoint (by
          intro h
          apply hij
          apply Fin.ext
          omega))))

theorem retainedChoiceUnion_inter_block
    {M K : ℕ} {b : Fin K → ℕ} {T : Fin K → Finset ℕ}
    (hT : T ∈ retainedBlockChoiceTuples M K b) (i : Fin K) :
    choiceUnion T ∩ retainedPrimeBlock (M + i) = T i := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpU, hpBlock⟩ := Finset.mem_inter.mp hp
    obtain ⟨j, hj, hpTj⟩ := Finset.mem_biUnion.mp hpU
    have hji : j = i := by
      by_contra hne
      exact (Finset.disjoint_left.mp
        (Disjoint.mono (retainedPrimeBlock_subset (M + j))
          (retainedPrimeBlock_subset (M + i))
          (primeBlock_pairwise_disjoint (by
            intro h
            apply hne
            apply Fin.ext
            omega))))
        ((mem_retainedBlockChoiceTuples.mp hT j).1 hpTj) hpBlock
    simpa [hji] using hpTj
  · intro hp
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hp⟩,
        (mem_retainedBlockChoiceTuples.mp hT i).1 hp⟩

theorem retainedChoiceUnion_mem_selection
    {M K : ℕ} {b : Fin K → ℕ} {T : Fin K → Finset ℕ}
    (hT : T ∈ retainedBlockChoiceTuples M K b) :
    choiceUnion T ∈ retainedBlockSelectionSets M K b := by
  rw [mem_retainedBlockSelectionSets]
  constructor
  · intro p hp
    obtain ⟨i, hi, hpTi⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_biUnion.mpr
      ⟨i.val, Finset.mem_range.mpr i.isLt,
        (mem_retainedBlockChoiceTuples.mp hT i).1 hpTi⟩
  · funext i
    rw [retainedBlockCountVector, retainedChoiceUnion_inter_block hT]
    exact (mem_retainedBlockChoiceTuples.mp hT i).2

theorem retainedChoiceUnion_injOn (M K : ℕ) (b : Fin K → ℕ) :
    Set.InjOn (choiceUnion (k := K)) (retainedBlockChoiceTuples M K b) := by
  intro T hT U hU hEq
  funext i
  rw [← retainedChoiceUnion_inter_block hT i,
    ← retainedChoiceUnion_inter_block hU i, hEq]

theorem image_retainedChoiceUnion_eq_selection
    (M K : ℕ) (b : Fin K → ℕ) :
    (retainedBlockChoiceTuples M K b).image choiceUnion =
      retainedBlockSelectionSets M K b := by
  ext S
  constructor
  · intro hS
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    exact retainedChoiceUnion_mem_selection hT
  · intro hS
    let T : Fin K → Finset ℕ :=
      fun i ↦ S ∩ retainedPrimeBlock (M + i)
    have hT : T ∈ retainedBlockChoiceTuples M K b := by
      rw [mem_retainedBlockChoiceTuples]
      intro i
      refine ⟨Finset.inter_subset_right, ?_⟩
      exact congrFun (mem_retainedBlockSelectionSets.mp hS).2 i
    refine Finset.mem_image.mpr ⟨T, hT, ?_⟩
    apply Finset.ext
    intro p
    constructor
    · intro hp
      obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
      exact (Finset.mem_inter.mp hp).1
    · intro hp
      have hpPool := (mem_retainedBlockSelectionSets.mp hS).1 hp
      obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hpPool
      let ii : Fin K := ⟨i, Finset.mem_range.mp hi⟩
      exact Finset.mem_biUnion.mpr
        ⟨ii, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hp, hpi⟩⟩

theorem selectionWeight_retainedChoiceUnion
    {M K : ℕ} {b : Fin K → ℕ} {T : Fin K → Finset ℕ}
    (hT : T ∈ retainedBlockChoiceTuples M K b) :
    selectionWeight (choiceUnion T) =
      ∏ i : Fin K, selectionWeight (T i) := by
  rw [selectionWeight, choiceUnion,
    Finset.prod_biUnion (retainedBlockChoice_pairwiseDisjoint hT)]
  rfl

/-- Elementary reciprocal mass inside one retained block. -/
noncomputable def retainedBlockElementaryMass (j r : ℕ) : ℝ :=
  ∑ S ∈ (retainedPrimeBlock j).powersetCard r, selectionWeight S

theorem retainedSelection_weight_factorization
    (M K : ℕ) (b : Fin K → ℕ) :
    (∑ S ∈ retainedBlockSelectionSets M K b, selectionWeight S) =
      ∏ i : Fin K, retainedBlockElementaryMass (M + i) (b i) := by
  rw [← image_retainedChoiceUnion_eq_selection M K b,
    Finset.sum_image (retainedChoiceUnion_injOn M K b)]
  calc
    (∑ T ∈ retainedBlockChoiceTuples M K b,
        selectionWeight (choiceUnion T)) =
        ∑ T ∈ retainedBlockChoiceTuples M K b,
          ∏ i : Fin K, selectionWeight (T i) := by
      apply Finset.sum_congr rfl
      intro T hT
      exact selectionWeight_retainedChoiceUnion hT
    _ = ∏ i : Fin K, retainedBlockElementaryMass (M + i) (b i) := by
      rw [retainedBlockChoiceTuples]
      simp only [retainedBlockElementaryMass]
      rw [← Finset.prod_univ_sum]

theorem retainedBlockElementaryMass_upper (j r : ℕ) :
    retainedBlockElementaryMass j r ≤
      retainedPrimeBlockMass j ^ r / (r.factorial : ℝ) := by
  have h := factorial_mul_elementaryMass_le_pow_sum
    (retainedPrimeBlock j) (fun p : ℕ ↦ 1 / (p : ℝ))
    (fun p hp ↦ by positivity) r
  have hfac : (0 : ℝ) < r.factorial := by positivity
  apply (le_div_iff₀ hfac).2
  have hterm (S : Finset ℕ) :
      subsetWeight (fun p : ℕ ↦ 1 / (p : ℝ)) S = selectionWeight S := by
    rfl
  simpa only [retainedBlockElementaryMass, elementaryMass,
    retainedPrimeBlockMass, hterm, mul_comm] using h

theorem retainedSelection_weight_le_weightedComposition
    (M : ℕ) {K : ℕ} (b : Fin K → ℕ) :
    (∑ S ∈ retainedBlockSelectionSets M K b, selectionWeight S) ≤
      weightedCompositionMass
        (fun i : Fin K ↦ retainedPrimeBlockMass (M + i)) b := by
  rw [retainedSelection_weight_factorization,
    weightedCompositionMass, compositionFactorial,
    ← Finset.prod_div_distrib]
  apply Finset.prod_le_prod
  · intro i hi
    exact Finset.sum_nonneg fun S hS ↦ by
      dsimp [selectionWeight]
      positivity
  · intro i hi
    exact retainedBlockElementaryMass_upper (M + i) (b i)

/-- Cluster mass of a retained block-count class. -/
noncomputable def retainedCompositionBlockClusterMass
    (M : ℕ) {K : ℕ} (b : Fin K → ℕ) : ℝ :=
  ∑ S ∈ retainedBlockSelectionSets M K b,
    clusterLength (S.prod id) / ((S.prod id : ℕ) : ℝ)

noncomputable def retainedBlockClusterMassOver
    (M : ℕ) {K : ℕ} (I : Finset (Fin K → ℕ)) : ℝ :=
  ∑ b ∈ I, retainedCompositionBlockClusterMass M b

theorem retainedCompositionBlockClusterMass_nonneg
    (M : ℕ) {K : ℕ} (b : Fin K → ℕ) :
    0 ≤ retainedCompositionBlockClusterMass M b := by
  apply Finset.sum_nonneg
  intro S hS
  exact div_nonneg (clusterLength_nonneg _) (by positivity)

theorem retainedCompositionBlockClusterMass_le
    {M K k : ℕ} {b : Fin K → ℕ}
    (_hb : ∑ i : Fin K, b i = k) {A : ℝ} (hA : 0 ≤ A)
    (henvelope : ∀ a ∈ compositionBlockFamily M b,
      clusterLength a ≤ A) :
    retainedCompositionBlockClusterMass M b ≤
      A * weightedCompositionMass
        (fun i : Fin K ↦ retainedPrimeBlockMass (M + i)) b := by
  have hweight := retainedSelection_weight_le_weightedComposition M b
  calc
    retainedCompositionBlockClusterMass M b ≤
        A * (∑ S ∈ retainedBlockSelectionSets M K b,
          selectionWeight S) := by
      rw [retainedCompositionBlockClusterMass, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro S hS
      have hOrig := retainedBlockSelectionSets_subset_original hS
      have hpos := selectionProduct_pos hOrig
      rw [div_eq_mul_inv, ← one_div,
        ← selectionWeight_eq_inv_product]
      exact mul_le_mul_of_nonneg_right
        (henvelope (S.prod id) (by
          change S.prod id ∈ blockFamily M K (extendComposition b)
          exact mem_blockFamily.mpr ⟨S, hOrig, rfl⟩)) (by
            dsimp [selectionWeight]
            positivity)
    _ ≤ A * weightedCompositionMass
        (fun i : Fin K ↦ retainedPrimeBlockMass (M + i)) b :=
      mul_le_mul_of_nonneg_left hweight hA

theorem retainedBlockIntegerDyadicLayer_mass_le
    {M k K m : ℕ} :
    retainedBlockClusterMassOver M (blockIntegerDyadicLayer k K m) ≤
      (sharpBlockLayerScale M * (2 : ℝ) ^ (k - m + 1)) *
        Real.log 2 ^ k *
          reciprocalFactorialMassOver
            (fordWeightedOccupancies k K m) := by
  let lam : Fin K → ℝ :=
    fun i ↦ retainedPrimeBlockMass (M + i)
  let A : ℝ := sharpBlockLayerScale M * (2 : ℝ) ^ (k - m + 1)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (sharpBlockLayerScale_pos M).le (by positivity)
  have hlam0 : ∀ i, 0 ≤ lam i := by
    intro i
    dsimp [lam, retainedPrimeBlockMass]
    positivity
  have hlam : ∀ i, lam i ≤ Real.log 2 := by
    intro i
    exact retainedPrimeBlockMass_le_log_two (M + i)
  calc
    retainedBlockClusterMassOver M (blockIntegerDyadicLayer k K m) ≤
        A * weightedOccupancyMassOver lam
          (blockIntegerDyadicLayer k K m) := by
      rw [retainedBlockClusterMassOver, weightedOccupancyMassOver,
        Finset.mul_sum]
      apply Finset.sum_le_sum
      intro b hb
      have hbSum := (mem_blockIntegerDyadicLayer.mp hb).1
      exact retainedCompositionBlockClusterMass_le hbSum hA
        (fun a ha ↦ blockIntegerDyadicLayer_clusterLength_le hb ha)
    _ ≤ A * (Real.log 2 ^ k * reciprocalFactorialMassOver
          (blockIntegerDyadicLayer k K m)) := by
      exact mul_le_mul_of_nonneg_left
        (weightedOccupancyMassOver_le_logTwo_pow hlam0 hlam
          (Finset.filter_subset _ _)) hA
    _ ≤ A * (Real.log 2 ^ k * reciprocalFactorialMassOver
          (fordWeightedOccupancies k K m)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact reciprocalFactorialMassOver_mono
        (blockIntegerDyadicLayer_subset_fordWeightedOccupancies k K m)
    _ = (sharpBlockLayerScale M * (2 : ℝ) ^ (k - m + 1)) *
        Real.log 2 ^ k * reciprocalFactorialMassOver
          (fordWeightedOccupancies k K m) := by
      dsimp [A]
      ring

/-- The complete retained fixed-cardinality mass after summing every
canonical layer. -/
theorem retainedBlockClusterMassOver_compositions_le_central
    {M k K : ℕ} (hK : 0 < K) (hkK : k ≤ 10 * K) :
    retainedBlockClusterMassOver M (compositionsOf K k) ≤
      sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) *
        Real.log 2 ^ k *
          (fordWeightedLayerMassConstant *
            fordCentralDepthTerm (K : ℝ) K k) := by
  simp only [retainedBlockClusterMassOver]
  rw [← sum_blockIntegerDyadicLayers k K
    (retainedCompositionBlockClusterMass M)]
  calc
    (∑ m ∈ Finset.range (k + 1),
        retainedBlockClusterMassOver M
          (blockIntegerDyadicLayer k K m)) ≤
        ∑ m ∈ Finset.range (k + 1),
          (sharpBlockLayerScale M * (2 : ℝ) ^ (k - m + 1)) *
            Real.log 2 ^ k * reciprocalFactorialMassOver
              (fordWeightedOccupancies k K m) := by
      exact Finset.sum_le_sum fun m hm ↦
        retainedBlockIntegerDyadicLayer_mass_le
    _ = sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) *
        Real.log 2 ^ k * fordWeightedLayerReciprocalSum k K := by
      rw [fordWeightedLayerReciprocalSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hmk : m ≤ k := by
        have := Finset.mem_range.mp hm
        omega
      have hp : (2 : ℝ) ^ (k - m + 1) =
          (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ m := by
        apply (eq_div_iff (by positivity : (2 : ℝ) ^ m ≠ 0)).2
        rw [← pow_add]
        congr 1
        omega
      rw [hp]
      ring
    _ ≤ sharpBlockLayerScale M * (2 : ℝ) ^ (k + 1) *
        Real.log 2 ^ k *
          (fordWeightedLayerMassConstant *
            fordCentralDepthTerm (K : ℝ) K k) := by
      exact mul_le_mul_of_nonneg_left
        (fordWeightedLayerReciprocalSum_le_central hK hkK) (by
          exact mul_nonneg
            (mul_nonneg (sharpBlockLayerScale_pos M).le (by positivity))
            (pow_nonneg (Real.log_pos one_lt_two).le k))

end

end Erdos446
