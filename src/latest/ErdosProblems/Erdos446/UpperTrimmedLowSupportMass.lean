/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperRetainedBlockMass
import ErdosProblems.Erdos446.UpperHighTail

/-!
# Erdős Problem 446: absorption of residual supports

Every smooth support is split uniquely into an auxiliary part (the fixed
small primes and all discarded residual primes) and a retained part.  The
cluster inequality `L(ab) ≤ τ(a)L(b)` charges the auxiliary support by
`2^ω(a)`.  Its complete squarefree sum is an Euler product, and the residual
piece of that product is uniformly bounded by the geometric trimming error.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable section

/-- Retained supports of cardinality at most `L`, expressed as a disjoint
union of exact-cardinality powersets. -/
def retainedLowSupportSet (M K L : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (L + 1)).biUnion fun k ↦
    (retainedPrimePool M K).powersetCard k

theorem mem_retainedLowSupportSet {M K L : ℕ} {S : Finset ℕ} :
    S ∈ retainedLowSupportSet M K L ↔
      S ⊆ retainedPrimePool M K ∧ S.card ≤ L := by
  simp only [retainedLowSupportSet, Finset.mem_biUnion,
    Finset.mem_range, Finset.mem_powersetCard]
  constructor
  · rintro ⟨k, hk, hS, hcard⟩
    exact ⟨hS, by omega⟩
  · rintro ⟨hS, hcard⟩
    exact ⟨S.card, by omega, hS, rfl⟩

theorem powersetCard_pairwiseDisjoint (P : Finset ℕ) (L : ℕ) :
    (↑(Finset.range (L + 1)) : Set ℕ).PairwiseDisjoint
      (fun k ↦ P.powersetCard k) := by
  intro i hi j hj hij
  change Disjoint (P.powersetCard i) (P.powersetCard j)
  rw [Finset.disjoint_left]
  intro S hSi hSj
  have hiCard := (Finset.mem_powersetCard.mp hSi).2
  have hjCard := (Finset.mem_powersetCard.mp hSj).2
  exact hij (hiCard.symm.trans hjCard)

theorem retainedLowSupport_clusterSum_eq
    (M K L : ℕ) :
    (∑ S ∈ retainedLowSupportSet M K L,
        clusterLength (S.prod id) / ((S.prod id : ℕ) : ℝ)) =
      ∑ k ∈ Finset.range (L + 1),
        retainedBlockClusterMassOver M (compositionsOf K k) := by
  rw [retainedLowSupportSet,
    Finset.sum_biUnion (powersetCard_pairwiseDisjoint
      (retainedPrimePool M K) L)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [retainedBlockClusterMassOver,
    ← retainedBlockSelectionSets_disjiUnion M K k,
    Finset.sum_disjiUnion]
  rfl

/-- The complete auxiliary squarefree cluster multiplier. -/
noncomputable def trimmedAuxiliaryClusterFactor (M K : ℕ) : ℝ :=
  ∑ Q ∈ (trimmedAuxiliaryPrimePool M K).powerset,
    (2 : ℝ) ^ Q.card * selectionWeight Q

theorem weightedPowerset_eq_eulerProduct (P : Finset ℕ) :
    (∑ Q ∈ P.powerset, (2 : ℝ) ^ Q.card * selectionWeight Q) =
      ∏ p ∈ P, (1 + 2 / (p : ℝ)) := by
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [selectionWeight, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  ring

theorem smallPrimeClusterFactor_eq_eulerProduct (M : ℕ) :
    smallPrimeClusterFactor M =
      ∏ p ∈ smallPrimePool M, (1 + 2 / (p : ℝ)) := by
  exact weightedPowerset_eq_eulerProduct (smallPrimePool M)

theorem trimmedAuxiliaryClusterFactor_nonneg (M K : ℕ) :
    0 ≤ trimmedAuxiliaryClusterFactor M K := by
  apply Finset.sum_nonneg
  intro Q hQ
  exact mul_nonneg (by positivity) (by
    dsimp [selectionWeight]
    positivity)

theorem trimmedAuxiliaryClusterFactor_le
    {C : ℝ} (hC : 0 ≤ C) {J M K : ℕ} (hJM : J ≤ M)
    (hmass : ∀ j : ℕ, J ≤ j →
      |primeBlockMass j - Real.log 2| ≤ C / (2 : ℝ) ^ j) :
    trimmedAuxiliaryClusterFactor M K ≤
      smallPrimeClusterFactor M *
        Real.exp (4 * (C + 1) / (2 : ℝ) ^ M) := by
  rw [trimmedAuxiliaryClusterFactor,
    weightedPowerset_eq_eulerProduct,
    trimmedAuxiliaryPrimePool,
    Finset.prod_union (smallPrimePool_disjoint_blockPool M K |>.mono_right
      (residualPrimePool_subset_blockPool M K)),
    ← smallPrimeClusterFactor_eq_eulerProduct]
  exact mul_le_mul_of_nonneg_left
    (residualSupport_eulerProduct_le hC hJM hmass
      (S := residualPrimePool M K) (by rfl))
    (smallPrimeClusterFactor_nonneg M)

/-- Pairs consisting of an arbitrary auxiliary support and a retained
support of cardinality at most `L`. -/
def trimmedLowSupportPairs (M K L : ℕ) :
    Finset (Finset ℕ × Finset ℕ) :=
  (trimmedAuxiliaryPrimePool M K).powerset.product
    (retainedLowSupportSet M K L)

def joinTrimmedSupport (QR : Finset ℕ × Finset ℕ) : Finset ℕ :=
  QR.1 ∪ QR.2

def splitTrimmedSupport (M K : ℕ) (S : Finset ℕ) :
    Finset ℕ × Finset ℕ :=
  (S ∩ trimmedAuxiliaryPrimePool M K,
    S ∩ retainedPrimePool M K)

theorem join_splitTrimmedSupport
    {M K : ℕ} {S : Finset ℕ}
    (hS : S ⊆ trimmedAuxiliaryPrimePool M K ∪ retainedPrimePool M K) :
    joinTrimmedSupport (splitTrimmedSupport M K S) = S := by
  rw [joinTrimmedSupport, splitTrimmedSupport,
    ← Finset.inter_union_distrib_left,
    Finset.inter_eq_left.mpr hS]

theorem splitTrimmedSupport_injOn
    {M K P k : ℕ}
    (hP : primesUpTo P ⊆
      trimmedAuxiliaryPrimePool M K ∪ retainedPrimePool M K) :
    Set.InjOn (splitTrimmedSupport M K) (smoothPrimeSubsets P k) := by
  intro S hS T hT hEq
  have hSsub : S ⊆
      trimmedAuxiliaryPrimePool M K ∪ retainedPrimePool M K :=
    (Finset.mem_powersetCard.mp hS).1.trans hP
  have hTsub : T ⊆
      trimmedAuxiliaryPrimePool M K ∪ retainedPrimePool M K :=
    (Finset.mem_powersetCard.mp hT).1.trans hP
  rw [← join_splitTrimmedSupport hSsub,
    ← join_splitTrimmedSupport hTsub, hEq]

theorem splitTrimmedSupport_mem_pairs
    {M K P k L : ℕ} (hkL : k ≤ L)
    (_hP : primesUpTo P ⊆
      trimmedAuxiliaryPrimePool M K ∪ retainedPrimePool M K)
    {S : Finset ℕ} (hS : S ∈ smoothPrimeSubsets P k) :
    splitTrimmedSupport M K S ∈ trimmedLowSupportPairs M K L := by
  exact Finset.mem_product.mpr ⟨
    Finset.mem_powerset.mpr Finset.inter_subset_right,
    mem_retainedLowSupportSet.mpr ⟨Finset.inter_subset_right, by
      have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
      calc
        (S ∩ retainedPrimePool M K).card ≤ S.card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = k := hcard
        _ ≤ L := hkL⟩⟩

theorem primesUpTo_two_mul_subset_trimmed_union_retained
    {M y : ℕ} (hy : fordConstructionScale M 1 ≤ y) :
    primesUpTo (2 * y) ⊆
      trimmedAuxiliaryPrimePool M (upperPrimeBlockCount M y) ∪
        retainedPrimePool M (upperPrimeBlockCount M y) := by
  rw [trimmedAuxiliaryPrimePool_union_retainedPrimePool]
  exact primesUpTo_two_mul_subset_small_union_upperBlocks hy

theorem joinedTrimmedSupport_clusterTerm_le
    {M K : ℕ} {Q R : Finset ℕ}
    (hQ : Q ⊆ trimmedAuxiliaryPrimePool M K)
    (hR : R ⊆ retainedPrimePool M K) :
    clusterLength ((Q ∪ R).prod id) /
        (((Q ∪ R).prod id : ℕ) : ℝ) ≤
      ((2 : ℝ) ^ Q.card * selectionWeight Q) *
        (clusterLength (R.prod id) / ((R.prod id : ℕ) : ℝ)) := by
  have hQend : Q ⊆ primesUpTo (blockEndpoint (M + K)) := by
    intro p hp
    rw [primesUpTo_endpoint_eq_trimmed_union_retained M K]
    exact Finset.mem_union_left _ (hQ hp)
  have hRend : R ⊆ primesUpTo (blockEndpoint (M + K)) := by
    intro p hp
    rw [primesUpTo_endpoint_eq_trimmed_union_retained M K]
    exact Finset.mem_union_right _ (hR hp)
  have hQpos : 0 < Q.prod id := primeProduct_pos hQend
  have hRpos : 0 < R.prod id := primeProduct_pos hRend
  have hQsq : Squarefree (Q.prod id) := primeProduct_squarefree hQend
  have hQpf : (Q.prod id).primeFactors = Q :=
    primeProduct_primeFactors hQend
  have hdisj : Disjoint Q R :=
    Finset.disjoint_of_subset_left hQ
      (Finset.disjoint_of_subset_right hR
        (trimmedAuxiliaryPrimePool_disjoint_retainedPrimePool M K))
  have hcard : (Q.prod id).divisors.card = 2 ^ Q.card := by
    rw [card_divisors_eq_two_pow_primeFactors_card hQpos hQsq, hQpf]
  have hcluster : clusterLength (R.prod id * Q.prod id) ≤
      ((Q.prod id).divisors.card : ℝ) * clusterLength (R.prod id) :=
    clusterLength_mul_le_card_divisors_mul_clusterLength hRpos hQpos
  have hprod : (Q ∪ R).prod id = R.prod id * Q.prod id := by
    rw [Finset.prod_union hdisj, mul_comm]
  have hweightQ : (((Q.prod id : ℕ) : ℝ))⁻¹ = selectionWeight Q := by
    simpa only [one_div] using (selectionWeight_eq_inv_product Q).symm
  have hweightR : (((R.prod id : ℕ) : ℝ))⁻¹ = selectionWeight R := by
    simpa only [one_div] using (selectionWeight_eq_inv_product R).symm
  rw [hcard] at hcluster
  push_cast at hcluster
  have hweights : 0 ≤ selectionWeight Q * selectionWeight R := by
    dsimp [selectionWeight]
    positivity
  rw [hprod, Nat.cast_mul]
  calc
    clusterLength (R.prod id * Q.prod id) /
        (((R.prod id : ℕ) : ℝ) * ((Q.prod id : ℕ) : ℝ)) =
      clusterLength (R.prod id * Q.prod id) *
        (selectionWeight Q * selectionWeight R) := by
      rw [div_eq_mul_inv, mul_inv_rev, hweightQ, hweightR]
    _ ≤
      ((2 : ℝ) ^ Q.card * clusterLength (R.prod id)) *
        (selectionWeight Q * selectionWeight R) :=
      mul_le_mul_of_nonneg_right hcluster hweights
    _ = ((2 : ℝ) ^ Q.card * selectionWeight Q) *
        (clusterLength (R.prod id) /
          ((R.prod id : ℕ) : ℝ)) := by
      rw [div_eq_mul_inv, hweightR]
      ring

/-- One low squarefree layer is injected into the auxiliary/retained pair
family without losing any term. -/
theorem squarefreeClusterLayer_le_trimmedLowPairs
    {M K P k L : ℕ} (hkL : k ≤ L)
    (hP : primesUpTo P ⊆
      trimmedAuxiliaryPrimePool M K ∪ retainedPrimePool M K) :
    squarefreeClusterLayer P k ≤
      ∑ QR ∈ trimmedLowSupportPairs M K L,
        clusterLength ((joinTrimmedSupport QR).prod id) /
          (((joinTrimmedSupport QR).prod id : ℕ) : ℝ) := by
  let f : Finset ℕ → ℝ := fun S ↦
    clusterLength (S.prod id) / ((S.prod id : ℕ) : ℝ)
  have hinj := splitTrimmedSupport_injOn (M := M) (K := K)
    (k := k) hP
  have himage : (smoothPrimeSubsets P k).image
      (splitTrimmedSupport M K) ⊆ trimmedLowSupportPairs M K L := by
    intro QR hQR
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hQR
    exact splitTrimmedSupport_mem_pairs hkL hP hS
  have heq : squarefreeClusterLayer P k =
      ∑ QR ∈ (smoothPrimeSubsets P k).image
          (splitTrimmedSupport M K), f (joinTrimmedSupport QR) := by
    rw [squarefreeClusterLayer, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro S hS
    dsimp [f]
    rw [join_splitTrimmedSupport
      ((Finset.mem_powersetCard.mp hS).1.trans hP)]
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg himage
    (fun QR hQR hnot ↦ div_nonneg (clusterLength_nonneg _) (by positivity))

/-- All low layers are charged only once to the auxiliary/retained pair
family. -/
theorem sum_lowSquarefreeClusterLayers_le_trimmedPairs
    {M K P L : ℕ}
    (hP : primesUpTo P ⊆
      trimmedAuxiliaryPrimePool M K ∪ retainedPrimePool M K) :
    (∑ k ∈ Finset.range (L + 1), squarefreeClusterLayer P k) ≤
      ∑ QR ∈ trimmedLowSupportPairs M K L,
        clusterLength ((joinTrimmedSupport QR).prod id) /
          (((joinTrimmedSupport QR).prod id : ℕ) : ℝ) := by
  -- Rewrite all low layers as one support family before applying the unique
  -- retained/auxiliary split, so no pair is charged more than once.
  let lowSupports : Finset (Finset ℕ) :=
    (Finset.range (L + 1)).biUnion fun k ↦ smoothPrimeSubsets P k
  have hpairwise : (↑(Finset.range (L + 1)) : Set ℕ).PairwiseDisjoint
      (smoothPrimeSubsets P) := by
    exact powersetCard_pairwiseDisjoint (primesUpTo P) L
  have hsum : (∑ k ∈ Finset.range (L + 1), squarefreeClusterLayer P k) =
      ∑ S ∈ lowSupports,
        clusterLength (S.prod id) / ((S.prod id : ℕ) : ℝ) := by
    dsimp [lowSupports]
    rw [Finset.sum_biUnion hpairwise]
    rfl
  have hcard (S : Finset ℕ) (hS : S ∈ lowSupports) : S.card ≤ L := by
    obtain ⟨k, hk, hSk⟩ := Finset.mem_biUnion.mp hS
    have := (Finset.mem_powersetCard.mp hSk).2
    have hk' := Finset.mem_range.mp hk
    omega
  have hsub (S : Finset ℕ) (hS : S ∈ lowSupports) :
      S ⊆ primesUpTo P := by
    obtain ⟨k, hk, hSk⟩ := Finset.mem_biUnion.mp hS
    exact (Finset.mem_powersetCard.mp hSk).1
  have hinj : Set.InjOn (splitTrimmedSupport M K) lowSupports := by
    intro S hS T hT hEq
    rw [← join_splitTrimmedSupport ((hsub S hS).trans hP),
      ← join_splitTrimmedSupport ((hsub T hT).trans hP), hEq]
  have himage : lowSupports.image (splitTrimmedSupport M K) ⊆
      trimmedLowSupportPairs M K L := by
    intro QR hQR
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hQR
    exact Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
      mem_retainedLowSupportSet.mpr
        ⟨Finset.inter_subset_right,
          (Finset.card_le_card Finset.inter_subset_left).trans (hcard S hS)⟩⟩
  rw [hsum]
  calc
    (∑ S ∈ lowSupports,
        clusterLength (S.prod id) / ((S.prod id : ℕ) : ℝ)) =
      ∑ QR ∈ lowSupports.image (splitTrimmedSupport M K),
        clusterLength ((joinTrimmedSupport QR).prod id) /
          (((joinTrimmedSupport QR).prod id : ℕ) : ℝ) := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro S hS
      rw [join_splitTrimmedSupport ((hsub S hS).trans hP)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg himage
      (fun QR hQR hnot ↦ div_nonneg (clusterLength_nonneg _) (by positivity))

theorem trimmedLowPairs_clusterMass_le
    (M K L : ℕ) :
    (∑ QR ∈ trimmedLowSupportPairs M K L,
        clusterLength ((joinTrimmedSupport QR).prod id) /
          (((joinTrimmedSupport QR).prod id : ℕ) : ℝ)) ≤
      trimmedAuxiliaryClusterFactor M K *
        (∑ k ∈ Finset.range (L + 1),
          retainedBlockClusterMassOver M (compositionsOf K k)) := by
  rw [trimmedLowSupportPairs]
  calc
    (∑ QR ∈ (trimmedAuxiliaryPrimePool M K).powerset.product
        (retainedLowSupportSet M K L),
        clusterLength ((joinTrimmedSupport QR).prod id) /
          (((joinTrimmedSupport QR).prod id : ℕ) : ℝ)) =
      ∑ Q ∈ (trimmedAuxiliaryPrimePool M K).powerset,
        ∑ R ∈ retainedLowSupportSet M K L,
          clusterLength ((Q ∪ R).prod id) /
            (((Q ∪ R).prod id : ℕ) : ℝ) := by
      simpa only [joinTrimmedSupport, Finset.product_eq_sprod] using
        (Finset.sum_product (trimmedAuxiliaryPrimePool M K).powerset
          (retainedLowSupportSet M K L)
          (fun QR ↦ clusterLength ((QR.1 ∪ QR.2).prod id) /
            (((QR.1 ∪ QR.2).prod id : ℕ) : ℝ)))
    _ ≤ ∑ Q ∈ (trimmedAuxiliaryPrimePool M K).powerset,
        ∑ R ∈ retainedLowSupportSet M K L,
          ((2 : ℝ) ^ Q.card * selectionWeight Q) *
            (clusterLength (R.prod id) / ((R.prod id : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro Q hQ
      apply Finset.sum_le_sum
      intro R hR
      exact joinedTrimmedSupport_clusterTerm_le
        (Finset.mem_powerset.mp hQ)
        (mem_retainedLowSupportSet.mp hR).1
    _ = trimmedAuxiliaryClusterFactor M K *
        (∑ R ∈ retainedLowSupportSet M K L,
          clusterLength (R.prod id) / ((R.prod id : ℕ) : ℝ)) := by
      rw [trimmedAuxiliaryClusterFactor, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [Finset.mul_sum]
    _ = trimmedAuxiliaryClusterFactor M K *
        (∑ k ∈ Finset.range (L + 1),
          retainedBlockClusterMassOver M (compositionsOf K k)) := by
      rw [retainedLowSupport_clusterSum_eq M K L]

end

end Erdos446
