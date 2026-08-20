/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperEnvelopeMassBridge
import ErdosProblems.Erdos446.ClusterProductSharp

/-!
# Erdős Problem 446: exact partition of smooth squarefree supports

The upper-bound argument separates the finitely many primes below the first
late Mertens block and then records, without replacing any block by a common
majorant, how many of the remaining prime factors lie in each consecutive
doubly-exponential block.  This file supplies that exact finite bookkeeping.

In particular, `smoothSupport_eq_small_union_blocks` says that *every* prime
which can occur in a squarefree integer below the terminal smoothness cutoff
is either a small prime or lies in exactly one of the selected blocks.
`blockSelectionSets_disjiUnion` then partitions all large-prime supports by
their block-count vectors.  Finally `blockSupportClusterMass_le_product`
retains the individual reciprocal masses `primeBlockMass (M+i)`; no uniform
enlargement (and hence no exponential loss) is made.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The finitely many primes at or below the first retained block endpoint. -/
def smallPrimePool (M : ℕ) : Finset ℕ :=
  primesUpTo (blockEndpoint M)

/-- The vector recording the exact number of selected primes in each block. -/
def blockCountVector (M : ℕ) {K : ℕ} (S : Finset ℕ) : Fin K → ℕ :=
  fun i ↦ (S ∩ primeBlock (M + i)).card

/-- Precisely the block-count vectors which occur among subsets of the block
pool.  Using the image, rather than an artificially large box, makes the
partition theorem below immediate and exact. -/
def occurringBlockCountVectors (M K : ℕ) : Finset (Fin K → ℕ) :=
  (blockPool M K).powerset.image (blockCountVector M)

theorem primesUpTo_eq_primesLE (N : ℕ) :
    primesUpTo N = Nat.primesLE N := by
  ext p
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc,
    Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp2, hpN⟩, hp⟩
    exact ⟨hpN, hp⟩
  · rintro ⟨hpN, hp⟩
    exact ⟨⟨hp.two_le, hpN⟩, hp⟩

theorem blockPool_succ (M K : ℕ) :
    blockPool M (K + 1) = blockPool M K ∪ primeBlock (M + K) := by
  ext p
  simp only [blockPool, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_union]
  constructor
  · rintro ⟨i, hi, hp⟩
    by_cases hiK : i < K
    · exact Or.inl ⟨i, hiK, hp⟩
    · have hik : i = K := by omega
      exact Or.inr (by simpa [hik] using hp)
  · rintro (h | hp)
    · obtain ⟨i, hi, hp⟩ := h
      exact ⟨i, by omega, hp⟩
    · exact ⟨K, by omega, hp⟩

/-- Membership in the union of consecutive prime blocks, stated only in
terms of its two terminal endpoints. -/
theorem mem_blockPool_iff_endpoint {M K p : ℕ} :
    p ∈ blockPool M K ↔
      p.Prime ∧ blockEndpoint M < p ∧ p ≤ blockEndpoint (M + K) := by
  induction K with
  | zero => simp [blockPool]
  | succ K ih =>
      rw [show K + 1 = K + 1 by rfl, blockPool_succ,
        Finset.mem_union, ih, mem_primeBlock]
      constructor
      · rintro (h | h)
        · exact ⟨h.1, h.2.1,
            h.2.2.trans (blockEndpoint_mono (by omega))⟩
        · exact ⟨h.1,
            lt_of_le_of_lt (blockEndpoint_mono (by omega)) h.2.1,
            by simpa [add_assoc] using h.2.2⟩
      · rintro ⟨hp, hpM, hpTop⟩
        by_cases hmid : p ≤ blockEndpoint (M + K)
        · exact Or.inl ⟨hp, hpM, hmid⟩
        · exact Or.inr ⟨hp, lt_of_not_ge hmid,
            by simpa [add_assoc] using hpTop⟩

theorem smallPrimePool_disjoint_blockPool (M K : ℕ) :
    Disjoint (smallPrimePool M) (blockPool M K) := by
  rw [Finset.disjoint_left]
  intro p hpSmall hpBlock
  have hs : p ≤ blockEndpoint M := by
    rw [smallPrimePool, primesUpTo_eq_primesLE] at hpSmall
    exact (Nat.mem_primesLE.mp hpSmall).1
  exact (not_lt_of_ge hs) (mem_blockPool_iff_endpoint.mp hpBlock).2.1

/-- All primes up to the terminal endpoint are the disjoint union of the
fixed small-prime pool and the retained consecutive blocks. -/
theorem smoothSupport_eq_small_union_blocks (M K : ℕ) :
    primesUpTo (blockEndpoint (M + K)) =
      smallPrimePool M ∪ blockPool M K := by
  ext p
  rw [Finset.mem_union]
  simp only [smallPrimePool, primesUpTo_eq_primesLE, Nat.mem_primesLE,
    mem_blockPool_iff_endpoint]
  constructor
  · rintro ⟨hpTop, hp⟩
    by_cases hsmall : p ≤ blockEndpoint M
    · exact Or.inl ⟨hsmall, hp⟩
    · exact Or.inr ⟨hp, lt_of_not_ge hsmall, hpTop⟩
  · rintro (h | h)
    · exact ⟨h.1.trans (blockEndpoint_mono (by omega)), h.2⟩
    · exact ⟨h.2.2, h.1⟩

/-- Small-prime part of a prime support. -/
def smallSupport (M : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S ∩ smallPrimePool M

/-- Part of a prime support lying in the retained consecutive blocks. -/
def largeBlockSupport (M K : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S ∩ blockPool M K

theorem support_eq_smallSupport_union_largeBlockSupport
    {M K : ℕ} {S : Finset ℕ}
    (hS : S ⊆ primesUpTo (blockEndpoint (M + K))) :
    S = smallSupport M S ∪ largeBlockSupport M K S := by
  rw [smallSupport, largeBlockSupport, ← Finset.inter_union_distrib_left,
    ← smoothSupport_eq_small_union_blocks]
  exact (Finset.inter_eq_left.mpr hS).symm

theorem smallSupport_disjoint_largeBlockSupport
    (M K : ℕ) (S : Finset ℕ) :
    Disjoint (smallSupport M S) (largeBlockSupport M K S) :=
  Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right
      (smallPrimePool_disjoint_blockPool M K))

theorem smallSupport_mem_powerset
    (M : ℕ) (S : Finset ℕ) :
    smallSupport M S ∈ (smallPrimePool M).powerset :=
  Finset.mem_powerset.mpr Finset.inter_subset_right

theorem largeBlockSupport_mem_selection
    {M K : ℕ} (S : Finset ℕ) :
    largeBlockSupport M K S ∈
      blockSelectionSets M K
        (extendComposition
          (blockCountVector (K := K) M (largeBlockSupport M K S))) :=
  by
    rw [mem_blockSelectionSets]
    refine ⟨Finset.inter_subset_right, ?_⟩
    intro i hi
    simp only [extendComposition, dif_pos hi, blockCountVector]

/-- Reciprocal weights factor exactly across the fixed small-prime part and
the retained blocks. -/
theorem selectionWeight_small_mul_large
    {M K : ℕ} {S : Finset ℕ}
    (hS : S ⊆ primesUpTo (blockEndpoint (M + K))) :
    selectionWeight S =
      selectionWeight (smallSupport M S) *
        selectionWeight (largeBlockSupport M K S) := by
  calc
    selectionWeight S = selectionWeight
        (smallSupport M S ∪ largeBlockSupport M K S) := by
      rw [← support_eq_smallSupport_union_largeBlockSupport hS]
    _ = selectionWeight (smallSupport M S) *
        selectionWeight (largeBlockSupport M K S) := by
      rw [selectionWeight,
        Finset.prod_union (smallSupport_disjoint_largeBlockSupport M K S)]
      rfl

/-- The same exact factorization at the level of the represented squarefree
integer. -/
theorem supportProduct_small_mul_large
    {M K : ℕ} {S : Finset ℕ}
    (hS : S ⊆ primesUpTo (blockEndpoint (M + K))) :
    S.prod id =
      (smallSupport M S).prod id * (largeBlockSupport M K S).prod id := by
  calc
    S.prod id = (smallSupport M S ∪ largeBlockSupport M K S).prod id := by
      rw [← support_eq_smallSupport_union_largeBlockSupport hS]
    _ = (smallSupport M S).prod id *
        (largeBlockSupport M K S).prod id := by
      rw [Finset.prod_union
        (smallSupport_disjoint_largeBlockSupport M K S)]

/-- Exact coverage of every smooth squarefree integer by a small support and
one block-count class.  This is the arithmetic partition used before the
cluster envelope is summed. -/
theorem mem_smoothSquarefreeNumbers_iff_small_block
    {M K a : ℕ} :
    a ∈ smoothSquarefreeNumbers (blockEndpoint (M + K)) ↔
      ∃ Q ∈ (smallPrimePool M).powerset,
        ∃ b ∈ occurringBlockCountVectors M K,
          ∃ R ∈ blockSelectionSets M K (extendComposition b),
            (Q ∪ R).prod id = a := by
  constructor
  · intro ha
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
    have hSsub : S ⊆ primesUpTo (blockEndpoint (M + K)) :=
      Finset.mem_powerset.mp hS
    let Q := smallSupport M S
    let R := largeBlockSupport M K S
    let b := blockCountVector (K := K) M R
    refine ⟨Q, smallSupport_mem_powerset M S, b, ?_, R, ?_, ?_⟩
    · exact Finset.mem_image.mpr
        ⟨R, Finset.mem_powerset.mpr Finset.inter_subset_right, rfl⟩
    · exact largeBlockSupport_mem_selection S
    · rw [← support_eq_smallSupport_union_largeBlockSupport hSsub]
  · rintro ⟨Q, hQ, b, hb, R, hR, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨Q ∪ R, ?_, rfl⟩
    rw [Finset.mem_powerset, smoothSupport_eq_small_union_blocks]
    exact Finset.union_subset_union (Finset.mem_powerset.mp hQ)
      (mem_blockSelectionSets.mp hR).1

/-- Pairs consisting of an arbitrary small-prime support and an arbitrary
support in the retained blocks. -/
def smallBlockSupportPairs (M K : ℕ) :
    Finset (Finset ℕ × Finset ℕ) :=
  (smallPrimePool M).powerset.product (blockPool M K).powerset

/-- Reassemble the two disjoint parts of a prime support. -/
def joinSmallBlockSupport (QR : Finset ℕ × Finset ℕ) : Finset ℕ :=
  QR.1 ∪ QR.2

private theorem joinSmallBlockSupport_inter_small
    {M K : ℕ} {Q R : Finset ℕ}
    (hQ : Q ⊆ smallPrimePool M) (hR : R ⊆ blockPool M K) :
    (Q ∪ R) ∩ smallPrimePool M = Q := by
  ext p
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hpQ | hpR, hpSmall⟩
    · exact hpQ
    · exact False.elim ((Finset.disjoint_left.mp
          (smallPrimePool_disjoint_blockPool M K)) hpSmall (hR hpR))
  · intro hpQ
    exact ⟨Or.inl hpQ, hQ hpQ⟩

private theorem joinSmallBlockSupport_inter_large
    {M K : ℕ} {Q R : Finset ℕ}
    (hQ : Q ⊆ smallPrimePool M) (hR : R ⊆ blockPool M K) :
    (Q ∪ R) ∩ blockPool M K = R := by
  ext p
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hpQ | hpR, hpLarge⟩
    · exact False.elim ((Finset.disjoint_left.mp
          (smallPrimePool_disjoint_blockPool M K)) (hQ hpQ) hpLarge)
    · exact hpR
  · intro hpR
    exact ⟨Or.inr hpR, hR hpR⟩

theorem joinSmallBlockSupport_injOn (M K : ℕ) :
    Set.InjOn joinSmallBlockSupport (smallBlockSupportPairs M K) := by
  rintro ⟨Q, R⟩ hQR ⟨Q', R'⟩ hQR' heq
  have hQRp := Finset.mem_product.mp hQR
  have hQRp' := Finset.mem_product.mp hQR'
  have hQ := Finset.mem_powerset.mp hQRp.1
  have hR := Finset.mem_powerset.mp hQRp.2
  have hQ' := Finset.mem_powerset.mp hQRp'.1
  have hR' := Finset.mem_powerset.mp hQRp'.2
  apply Prod.ext
  · have h := congrArg
        (fun S : Finset ℕ ↦ S ∩ smallPrimePool M) heq
    simp only [joinSmallBlockSupport] at h
    rw [joinSmallBlockSupport_inter_small hQ hR,
      joinSmallBlockSupport_inter_small hQ' hR'] at h
    exact h
  · have h := congrArg
        (fun S : Finset ℕ ↦ S ∩ blockPool M K) heq
    simp only [joinSmallBlockSupport] at h
    rw [joinSmallBlockSupport_inter_large hQ hR,
      joinSmallBlockSupport_inter_large hQ' hR'] at h
    exact h

/-- Joining the two parts gives exactly the powerset of all primes below the
terminal endpoint. -/
theorem image_joinSmallBlockSupport (M K : ℕ) :
    (smallBlockSupportPairs M K).image joinSmallBlockSupport =
      (primesUpTo (blockEndpoint (M + K))).powerset := by
  ext S
  constructor
  · intro hS
    obtain ⟨⟨Q, R⟩, hQR, rfl⟩ := Finset.mem_image.mp hS
    rw [Finset.mem_powerset, smoothSupport_eq_small_union_blocks]
    exact Finset.union_subset_union
      (Finset.mem_powerset.mp (Finset.mem_product.mp hQR).1)
      (Finset.mem_powerset.mp (Finset.mem_product.mp hQR).2)
  · intro hS
    have hSsub := Finset.mem_powerset.mp hS
    refine Finset.mem_image.mpr
      ⟨⟨smallSupport M S, largeBlockSupport M K S⟩, ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨smallSupport_mem_powerset M S,
          Finset.mem_powerset.mpr Finset.inter_subset_right⟩
    · exact (support_eq_smallSupport_union_largeBlockSupport hSsub).symm

theorem mem_occurringBlockCountVectors {M K : ℕ} {b : Fin K → ℕ} :
    b ∈ occurringBlockCountVectors M K ↔
      ∃ S ⊆ blockPool M K, blockCountVector M S = b := by
  simp [occurringBlockCountVectors]

theorem mem_blockSelectionSets_iff_countVector
    {M K : ℕ} {b : Fin K → ℕ} {S : Finset ℕ} :
    S ∈ blockSelectionSets M K (extendComposition b) ↔
      S ⊆ blockPool M K ∧ blockCountVector M S = b := by
  rw [mem_blockSelectionSets]
  constructor
  · rintro ⟨hS, hcount⟩
    refine ⟨hS, funext fun i ↦ ?_⟩
    exact (hcount i i.isLt).trans (extendComposition_fin b i)
  · rintro ⟨hS, hb⟩
    refine ⟨hS, ?_⟩
    intro i hi
    have := congrFun hb ⟨i, hi⟩
    rw [extendComposition, dif_pos hi]
    simpa only [blockCountVector] using this

theorem blockSelectionSets_eq_countVectorFiber
    (M K : ℕ) (b : Fin K → ℕ) :
    blockSelectionSets M K (extendComposition b) =
      (blockPool M K).powerset.filter (blockCountVector M · = b) := by
  ext S
  simp only [mem_blockSelectionSets_iff_countVector, Finset.mem_filter,
    Finset.mem_powerset]

theorem occurringBlockCountVectors_pairwiseDisjoint (M K : ℕ) :
    ((occurringBlockCountVectors M K : Finset (Fin K → ℕ)) :
      Set (Fin K → ℕ)).PairwiseDisjoint
        (fun b ↦ blockSelectionSets M K (extendComposition b)) := by
  intro b hb c hc hbc
  change Disjoint (blockSelectionSets M K (extendComposition b))
    (blockSelectionSets M K (extendComposition c))
  rw [Finset.disjoint_left]
  intro S hSb hSc
  have hb' := (mem_blockSelectionSets_iff_countVector.mp hSb).2
  have hc' := (mem_blockSelectionSets_iff_countVector.mp hSc).2
  exact hbc (hb'.symm.trans hc')

/-- The exact disjoint partition of all large-prime squarefree supports by
their block-count vectors. -/
theorem blockSelectionSets_disjiUnion (M K : ℕ) :
    (occurringBlockCountVectors M K).disjiUnion
        (fun b ↦ blockSelectionSets M K (extendComposition b))
        (occurringBlockCountVectors_pairwiseDisjoint M K) =
      (blockPool M K).powerset := by
  ext S
  simp only [Finset.mem_disjiUnion, Finset.mem_powerset]
  constructor
  · rintro ⟨b, hb, hS⟩
    exact (mem_blockSelectionSets_iff_countVector.mp hS).1
  · intro hS
    refine ⟨blockCountVector M S, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨S, Finset.mem_powerset.mpr hS, rfl⟩
    · exact mem_blockSelectionSets_iff_countVector.mpr ⟨hS, rfl⟩

/-- Exact three-level sum decomposition: finite small-prime supports, then
block-count vectors, then supports with that vector.  No term is discarded
or estimated in this identity. -/
theorem smoothSupport_sum_eq_small_block_count_sum
    (M K : ℕ) (F : Finset ℕ → ℝ) :
    (∑ S ∈ (primesUpTo (blockEndpoint (M + K))).powerset, F S) =
      ∑ Q ∈ (smallPrimePool M).powerset,
        ∑ b ∈ occurringBlockCountVectors M K,
          ∑ R ∈ blockSelectionSets M K (extendComposition b),
            F (Q ∪ R) := by
  rw [← image_joinSmallBlockSupport M K,
    Finset.sum_image (joinSmallBlockSupport_injOn M K)]
  rw [smallBlockSupportPairs]
  calc
    (∑ QR ∈ (smallPrimePool M).powerset.product (blockPool M K).powerset,
        F (joinSmallBlockSupport QR)) =
        ∑ Q ∈ (smallPrimePool M).powerset,
          ∑ R ∈ (blockPool M K).powerset, F (Q ∪ R) := by
      simpa only [joinSmallBlockSupport, Finset.product_eq_sprod] using
        (Finset.sum_product (smallPrimePool M).powerset
          (blockPool M K).powerset
          (fun QR ↦ F (QR.1 ∪ QR.2)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [← blockSelectionSets_disjiUnion M K, Finset.sum_disjiUnion]

/-- Exact support-side form of `squarefreeClusterMass`. -/
theorem squarefreeClusterMass_eq_support_sum (P : ℕ) :
    squarefreeClusterMass P =
      ∑ S ∈ (primesUpTo P).powerset,
        clusterLength (S.prod id) / ((S.prod id : ℕ) : ℝ) := by
  rw [squarefreeClusterMass, smoothSquarefreeNumbers,
    Finset.sum_image (primeProduct_injOn P)]

/-- Consequently the entire smooth squarefree cluster mass is partitioned
exactly by the finite small-prime support and the large block-count vector. -/
theorem squarefreeClusterMass_eq_small_block_count_sum (M K : ℕ) :
    squarefreeClusterMass (blockEndpoint (M + K)) =
      ∑ Q ∈ (smallPrimePool M).powerset,
        ∑ b ∈ occurringBlockCountVectors M K,
          ∑ R ∈ blockSelectionSets M K (extendComposition b),
            clusterLength ((Q ∪ R).prod id) /
              (((Q ∪ R).prod id : ℕ) : ℝ) := by
  rw [squarefreeClusterMass_eq_support_sum,
    smoothSupport_sum_eq_small_block_count_sum]

/-- The finite Euler factor contributed by primes before the first retained
block.  For fixed `M` it is an absolute finite constant. -/
noncomputable def smallPrimeReciprocalFactor (M : ℕ) : ℝ :=
  ∑ Q ∈ (smallPrimePool M).powerset, selectionWeight Q

theorem smallPrimeReciprocalFactor_nonneg (M : ℕ) :
    0 ≤ smallPrimeReciprocalFactor M := by
  apply Finset.sum_nonneg
  intro Q hQ
  dsimp [selectionWeight]
  positivity

theorem selectionWeight_union_small_block
    {M K : ℕ} {Q R : Finset ℕ}
    (hQ : Q ⊆ smallPrimePool M) (hR : R ⊆ blockPool M K) :
    selectionWeight (Q ∪ R) = selectionWeight Q * selectionWeight R := by
  rw [selectionWeight, Finset.prod_union]
  · rfl
  · exact Finset.disjoint_of_subset_left hQ
      (Finset.disjoint_of_subset_right hR
        (smallPrimePool_disjoint_blockPool M K))

/-- For one block-count vector, summing over *all* finite small-prime
supports costs only `smallPrimeReciprocalFactor M`, while every large block
retains its own exact reciprocal mass. -/
theorem small_block_reciprocal_sum_le_nonuniform_product
    (M : ℕ) {K : ℕ} (b : Fin K → ℕ) :
    (∑ Q ∈ (smallPrimePool M).powerset,
        ∑ R ∈ blockSelectionSets M K (extendComposition b),
          1 / (((Q ∪ R).prod id : ℕ) : ℝ)) ≤
      smallPrimeReciprocalFactor M *
        ∏ i : Fin K,
          primeBlockMass (M + i) ^ b i /
            ((b i).factorial : ℝ) := by
  have hlarge :
      (∑ R ∈ blockSelectionSets M K (extendComposition b),
          selectionWeight R) ≤
        ∏ i : Fin K,
          primeBlockMass (M + i) ^ b i /
            ((b i).factorial : ℝ) := by
    rw [← blockFamily_reciprocal_sum M K (extendComposition b)]
    simpa only [extendComposition_fin] using
      blockFamily_reciprocal_sum_upper M K (extendComposition b)
  calc
    (∑ Q ∈ (smallPrimePool M).powerset,
        ∑ R ∈ blockSelectionSets M K (extendComposition b),
          1 / (((Q ∪ R).prod id : ℕ) : ℝ)) =
        ∑ Q ∈ (smallPrimePool M).powerset,
          ∑ R ∈ blockSelectionSets M K (extendComposition b),
            selectionWeight Q * selectionWeight R := by
      apply Finset.sum_congr rfl
      intro Q hQ
      apply Finset.sum_congr rfl
      intro R hR
      rw [← selectionWeight_eq_inv_product,
        selectionWeight_union_small_block
          (Finset.mem_powerset.mp hQ)
          (mem_blockSelectionSets.mp hR).1]
    _ = smallPrimeReciprocalFactor M *
        (∑ R ∈ blockSelectionSets M K (extendComposition b),
          selectionWeight R) := by
      rw [smallPrimeReciprocalFactor, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [Finset.mul_sum]
    _ ≤ smallPrimeReciprocalFactor M *
        ∏ i : Fin K,
          primeBlockMass (M + i) ^ b i /
            ((b i).factorial : ℝ) :=
      mul_le_mul_of_nonneg_left hlarge
        (smallPrimeReciprocalFactor_nonneg M)

/-- The finitely many small primes multiply the sharp large-block envelope
by at most `2^#Q`; in particular they do not alter the Smirnov exponent. -/
theorem small_union_block_clusterLength_le_sharpEnvelope
    {M K k : ℕ} {Q R : Finset ℕ} {b : Fin K → ℕ}
    (hQ : Q ∈ (smallPrimePool M).powerset)
    (hR : R ∈ blockSelectionSets M K (extendComposition b))
    (hb : ∑ i : Fin K, b i = k) :
    clusterLength ((Q ∪ R).prod id) ≤
      (2 : ℝ) ^ Q.card * blockClusterSharpEnvelope M k b := by
  have hQsub : Q ⊆ primesUpTo (blockEndpoint M) := by
    exact Finset.mem_powerset.mp hQ
  have hQpos : 0 < Q.prod id := primeProduct_pos hQsub
  have hQsq : Squarefree (Q.prod id) := primeProduct_squarefree hQsub
  have hQpf : (Q.prod id).primeFactors = Q :=
    primeProduct_primeFactors hQsub
  have hRpos : 0 < R.prod id := selectionProduct_pos hR
  have hQRdisj : Disjoint Q R :=
    Finset.disjoint_of_subset_left (Finset.mem_powerset.mp hQ)
      (Finset.disjoint_of_subset_right (mem_blockSelectionSets.mp hR).1
        (smallPrimePool_disjoint_blockPool M K))
  have hprod : (Q ∪ R).prod id = R.prod id * Q.prod id := by
    rw [Finset.prod_union hQRdisj, mul_comm]
  have hcard : (Q.prod id).divisors.card = 2 ^ Q.card := by
    rw [card_divisors_eq_two_pow_primeFactors_card hQpos hQsq, hQpf]
  rw [hprod]
  calc
    clusterLength (R.prod id * Q.prod id) ≤
        ((Q.prod id).divisors.card : ℝ) * clusterLength (R.prod id) :=
      clusterLength_mul_le_card_divisors_mul_clusterLength hRpos hQpos
    _ = (2 : ℝ) ^ Q.card * clusterLength (R.prod id) := by
      rw [hcard]
      push_cast
      rfl
    _ ≤ (2 : ℝ) ^ Q.card * blockClusterSharpEnvelope M k b := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact compositionBlock_clusterLength_le_sharpEnvelope hb
        (mem_blockFamily.mpr ⟨R, hR, rfl⟩)

/-- Cluster mass of one large block-count class with a fixed small-prime
support adjoined. -/
noncomputable def smallBlockSupportClusterMass
    (M : ℕ) {K : ℕ} (Q : Finset ℕ) (b : Fin K → ℕ) : ℝ :=
  ∑ R ∈ blockSelectionSets M K (extendComposition b),
    clusterLength ((Q ∪ R).prod id) /
      (((Q ∪ R).prod id : ℕ) : ℝ)

/-- Fixed-small-support cluster mass, with the exact nonuniform product of
prime-block masses retained. -/
theorem smallBlockSupportClusterMass_le_nonuniform_product
    {M K k : ℕ} {Q : Finset ℕ} {b : Fin K → ℕ}
    (hQ : Q ∈ (smallPrimePool M).powerset)
    (hb : ∑ i : Fin K, b i = k) :
    smallBlockSupportClusterMass M Q b ≤
      ((2 : ℝ) ^ Q.card * selectionWeight Q) *
        blockClusterSharpEnvelope M k b *
          ∏ i : Fin K,
            primeBlockMass (M + i) ^ b i /
              ((b i).factorial : ℝ) := by
  have hlarge :
      (∑ R ∈ blockSelectionSets M K (extendComposition b),
          selectionWeight R) ≤
        ∏ i : Fin K,
          primeBlockMass (M + i) ^ b i /
            ((b i).factorial : ℝ) := by
    rw [← blockFamily_reciprocal_sum M K (extendComposition b)]
    simpa only [extendComposition_fin] using
      blockFamily_reciprocal_sum_upper M K (extendComposition b)
  have hcoef : 0 ≤
      ((2 : ℝ) ^ Q.card * selectionWeight Q) *
        blockClusterSharpEnvelope M k b := by
    have hweight : 0 ≤ selectionWeight Q := by
      dsimp [selectionWeight]
      positivity
    exact mul_nonneg (mul_nonneg (by positivity) hweight)
      (blockClusterSharpEnvelope_nonneg M k b)
  calc
    smallBlockSupportClusterMass M Q b ≤
        ∑ R ∈ blockSelectionSets M K (extendComposition b),
          (((2 : ℝ) ^ Q.card * selectionWeight Q) *
            blockClusterSharpEnvelope M k b) * selectionWeight R := by
      apply Finset.sum_le_sum
      intro R hR
      rw [div_eq_mul_inv, ← one_div,
        ← selectionWeight_eq_inv_product,
        selectionWeight_union_small_block
          (Finset.mem_powerset.mp hQ)
          (mem_blockSelectionSets.mp hR).1]
      have hcluster := small_union_block_clusterLength_le_sharpEnvelope
        hQ hR hb
      have hweights : 0 ≤ selectionWeight Q * selectionWeight R := by
        dsimp [selectionWeight]
        positivity
      calc
        clusterLength ((Q ∪ R).prod id) *
            (selectionWeight Q * selectionWeight R) ≤
          ((2 : ℝ) ^ Q.card * blockClusterSharpEnvelope M k b) *
            (selectionWeight Q * selectionWeight R) :=
          mul_le_mul_of_nonneg_right hcluster hweights
        _ = (((2 : ℝ) ^ Q.card * selectionWeight Q) *
            blockClusterSharpEnvelope M k b) * selectionWeight R := by ring
    _ = (((2 : ℝ) ^ Q.card * selectionWeight Q) *
          blockClusterSharpEnvelope M k b) *
        (∑ R ∈ blockSelectionSets M K (extendComposition b),
          selectionWeight R) := by rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ) ^ Q.card * selectionWeight Q) *
        blockClusterSharpEnvelope M k b *
          ∏ i : Fin K,
            primeBlockMass (M + i) ^ b i /
              ((b i).factorial : ℝ) :=
      mul_le_mul_of_nonneg_left hlarge hcoef

/-- The fixed finite constant which absorbs all primes before block `M` in
the sharp cluster-mass estimate. -/
noncomputable def smallPrimeClusterFactor (M : ℕ) : ℝ :=
  ∑ Q ∈ (smallPrimePool M).powerset,
    (2 : ℝ) ^ Q.card * selectionWeight Q

theorem smallPrimeClusterFactor_nonneg (M : ℕ) :
    0 ≤ smallPrimeClusterFactor M := by
  apply Finset.sum_nonneg
  intro Q hQ
  dsimp [selectionWeight]
  positivity

/-- After summing over every small-prime support, a block-count vector is
still bounded by the sharp envelope times the exact nonuniform block-mass
product; only the fixed finite factor `smallPrimeClusterFactor M` appears. -/
theorem sum_smallBlockSupportClusterMass_le_nonuniform_product
    {M K k : ℕ} {b : Fin K → ℕ}
    (hb : ∑ i : Fin K, b i = k) :
    (∑ Q ∈ (smallPrimePool M).powerset,
        smallBlockSupportClusterMass M Q b) ≤
      smallPrimeClusterFactor M * blockClusterSharpEnvelope M k b *
        ∏ i : Fin K,
          primeBlockMass (M + i) ^ b i /
            ((b i).factorial : ℝ) := by
  calc
    (∑ Q ∈ (smallPrimePool M).powerset,
        smallBlockSupportClusterMass M Q b) ≤
      ∑ Q ∈ (smallPrimePool M).powerset,
        ((2 : ℝ) ^ Q.card * selectionWeight Q) *
          blockClusterSharpEnvelope M k b *
            ∏ i : Fin K,
              primeBlockMass (M + i) ^ b i /
                ((b i).factorial : ℝ) := by
      exact Finset.sum_le_sum fun Q hQ ↦
        smallBlockSupportClusterMass_le_nonuniform_product hQ hb
    _ = smallPrimeClusterFactor M * blockClusterSharpEnvelope M k b *
        ∏ i : Fin K,
          primeBlockMass (M + i) ^ b i /
            ((b i).factorial : ℝ) := by
      rw [smallPrimeClusterFactor, Finset.sum_mul, Finset.sum_mul]

/-- Reordered exact cluster partition, exposing the quantity bounded by the
preceding theorem for each block-count vector. -/
theorem squarefreeClusterMass_eq_sum_smallBlockSupportClusterMass
    (M K : ℕ) :
    squarefreeClusterMass (blockEndpoint (M + K)) =
      ∑ b ∈ occurringBlockCountVectors M K,
        ∑ Q ∈ (smallPrimePool M).powerset,
          smallBlockSupportClusterMass M Q b := by
  rw [squarefreeClusterMass_eq_small_block_count_sum]
  simp only [smallBlockSupportClusterMass]
  rw [Finset.sum_comm]

/-- The same sharp nonuniform estimate after restricting to any finite layer
of count vectors of total size `k` (for example, a Smirnov barrier layer). -/
theorem sum_smallBlockSupportClusterMass_over_le
    {M K k : ℕ} {I : Finset (Fin K → ℕ)}
    (hI : ∀ b ∈ I, ∑ i : Fin K, b i = k) :
    (∑ b ∈ I, ∑ Q ∈ (smallPrimePool M).powerset,
        smallBlockSupportClusterMass M Q b) ≤
      smallPrimeClusterFactor M *
        ∑ b ∈ I,
          blockClusterSharpEnvelope M k b *
            ∏ i : Fin K,
              primeBlockMass (M + i) ^ b i /
                ((b i).factorial : ℝ) := by
  calc
    (∑ b ∈ I, ∑ Q ∈ (smallPrimePool M).powerset,
        smallBlockSupportClusterMass M Q b) ≤
      ∑ b ∈ I,
        smallPrimeClusterFactor M * blockClusterSharpEnvelope M k b *
          ∏ i : Fin K,
            primeBlockMass (M + i) ^ b i /
              ((b i).factorial : ℝ) := by
      exact Finset.sum_le_sum fun b hb ↦
        sum_smallBlockSupportClusterMass_le_nonuniform_product (hI b hb)
    _ = smallPrimeClusterFactor M *
        ∑ b ∈ I,
          blockClusterSharpEnvelope M k b *
            ∏ i : Fin K,
              primeBlockMass (M + i) ^ b i /
                ((b i).factorial : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring

/-- The reciprocal cluster mass written on prime supports rather than on
their injective products. -/
noncomputable def blockSupportClusterMass (M : ℕ) {K : ℕ}
    (b : Fin K → ℕ) : ℝ :=
  ∑ S ∈ blockSelectionSets M K (extendComposition b),
    clusterLength (S.prod id) / ((S.prod id : ℕ) : ℝ)

theorem blockSupportClusterMass_eq_compositionBlockClusterMass
    (M : ℕ) {K : ℕ} (b : Fin K → ℕ) :
    blockSupportClusterMass M b = compositionBlockClusterMass M b := by
  rw [blockSupportClusterMass, compositionBlockClusterMass,
    compositionBlockFamily, blockFamily,
    Finset.sum_image (selectionProduct_injOn M K (extendComposition b))]

/-- The sharp cluster envelope and exact nonuniform block masses combine
before any summation over count vectors. -/
theorem blockSupportClusterMass_le_product
    {M K : ℕ} {b : Fin K → ℕ} {k : ℕ}
    (hb : ∑ i : Fin K, b i = k) :
    blockSupportClusterMass M b ≤
      blockClusterSharpEnvelope M k b *
        ∏ i : Fin K,
          primeBlockMass (M + i) ^ b i /
            ((b i).factorial : ℝ) := by
  rw [blockSupportClusterMass_eq_compositionBlockClusterMass]
  apply compositionBlockClusterMass_le_product
  · rw [blockClusterSharpEnvelope]
    let F := (Finset.range (K + 1)).image
      (blockClusterSharpPrefixEnvelope M k b)
    have hF : F.Nonempty := by
      exact Finset.image_nonempty.mpr ⟨0, by simp⟩
    have hmem := Finset.min'_mem F hF
    obtain ⟨h, hh, heq⟩ := Finset.mem_image.mp hmem
    rw [← heq]
    dsimp [blockClusterSharpPrefixEnvelope]
    positivity
  · intro a ha
    exact compositionBlock_clusterLength_le_sharpEnvelope hb ha

/-- Summing over any finite collection of count vectors still retains the
individual block masses.  This is the form used when those vectors are next
partitioned into sharp-envelope/Smirnov layers. -/
theorem blockSupportClusterMass_sum_le_product
    {M K k : ℕ} {I : Finset (Fin K → ℕ)}
    (hI : ∀ b ∈ I, ∑ i : Fin K, b i = k) :
    (∑ b ∈ I, blockSupportClusterMass M b) ≤
      ∑ b ∈ I,
        blockClusterSharpEnvelope M k b *
          ∏ i : Fin K,
            primeBlockMass (M + i) ^ b i /
              ((b i).factorial : ℝ) := by
  exact Finset.sum_le_sum fun b hb ↦
    blockSupportClusterMass_le_product (hI b hb)

end Erdos446
