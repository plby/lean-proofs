/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos877.Deletion
import ErdosProblems.Erdos877.Binomial

/-!
# Erdős 877: the finite double count

This file packages the purely finite part of the Łuczak--Schoen argument. A
good deletion of a large maximal sum-free set produces a sum-free core. For a
fixed core, the deleted part is a subset of the points addable to that core;
moreover, the deleted part determines the original maximal set. Thus the
number of pairs is bounded by the number of sum-free cores times a power of
two.

The abundance of good deletions is proved separately in `Deletion.lean`.
-/

open Finset

namespace Erdos877

/-- Ambient points which can be adjoined individually to a sum-free core. -/
noncomputable def extensionCandidates (U S : Finset ℕ) : Finset ℕ :=
  U.filter (Addable S)

@[simp] theorem mem_extensionCandidates {U S : Finset ℕ} {x : ℕ} :
    x ∈ extensionCandidates U S ↔ x ∈ U ∧ Addable S x := by
  classical
  simp [extensionCandidates]

/-- Maximal sum-free sets in `[1,n]` whose size is at least `n / 10`. -/
noncomputable def largeMaximalSumFreeSets (n : ℕ) : Finset (Finset ℕ) :=
  (maximalSumFreeSets n).filter fun A ↦ n ≤ 10 * A.card

@[simp] theorem mem_largeMaximalSumFreeSets {n : ℕ} {A : Finset ℕ} :
    A ∈ largeMaximalSumFreeSets n ↔
      MaximalSumFreeIn (interval n) A ∧ n ≤ 10 * A.card := by
  classical
  simp [largeMaximalSumFreeSets]

/-- Deletions of the prescribed size whose core has at most
`2n / deletionDenominator` individually addable points. -/
noncomputable def countingGoodDeletions (n : ℕ) (A : Finset ℕ) : Finset (Finset ℕ) :=
  (A.powersetCard (A.card / (deletionDenom + 1))).filter fun B ↦
    (deletionDenom + 1) * (extensionCandidates (interval n) (A \ B)).card ≤ 2 * n

@[simp] theorem mem_countingGoodDeletions {n : ℕ} {A B : Finset ℕ} :
    B ∈ countingGoodDeletions n A ↔
      B ⊆ A ∧ B.card = A.card / (deletionDenom + 1) ∧
        (deletionDenom + 1) *
          (extensionCandidates (interval n) (A \ B)).card ≤ 2 * n := by
  classical
  simp [countingGoodDeletions, and_assoc]

theorem countingGoodDeletions_eq (n : ℕ) (A : Finset ℕ)
    (hA : MaximalSumFreeIn (interval n) A) :
    countingGoodDeletions n A =
      goodDeletionsWith (deletionDenom + 1) n A hA := by
  rfl

/-- The finite incidence set of a large maximal set and one of its good
deletions. -/
noncomputable def goodDeletionPairs (n : ℕ) :
    Finset (Finset ℕ × Finset ℕ) :=
  ((largeMaximalSumFreeSets n).product (interval n).powerset).filter fun p ↦
    p.2 ∈ countingGoodDeletions n p.1

@[simp] theorem mem_goodDeletionPairs {n : ℕ} {A B : Finset ℕ} :
    (A, B) ∈ goodDeletionPairs n ↔
      A ∈ largeMaximalSumFreeSets n ∧ B ∈ countingGoodDeletions n A := by
  classical
  constructor
  · intro h
    have hp := Finset.mem_filter.mp h
    exact ⟨(Finset.mem_product.mp hp.1).1, hp.2⟩
  · rintro ⟨hA, hB⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hA, ?_⟩, hB⟩
    exact Finset.mem_powerset.mpr
      ((mem_countingGoodDeletions.mp hB).1.trans
        (mem_largeMaximalSumFreeSets.mp hA).1.subset)

/-- The core left by a deletion pair. -/
def deletionCore (p : Finset ℕ × Finset ℕ) : Finset ℕ :=
  p.1 \ p.2

theorem deletionCore_mem_sumFreeSets {n : ℕ} {p : Finset ℕ × Finset ℕ}
    (hp : p ∈ goodDeletionPairs n) :
    deletionCore p ∈ sumFreeSets n := by
  rcases p with ⟨A, B⟩
  rw [mem_goodDeletionPairs] at hp
  have hmax := (mem_largeMaximalSumFreeSets.mp hp.1).1
  exact mem_sumFreeSets.mpr
    ⟨(sdiff_subset.trans hmax.subset), hmax.sumFree.mono sdiff_subset⟩

/-- In a good pair, every deleted point is individually addable to the core. -/
theorem deletion_subset_extensionCandidates {n : ℕ} {A B : Finset ℕ}
    (hp : (A, B) ∈ goodDeletionPairs n) :
    B ⊆ extensionCandidates (interval n) (A \ B) := by
  intro b hb
  rw [mem_extensionCandidates]
  rw [mem_goodDeletionPairs] at hp
  have hmax := (mem_largeMaximalSumFreeSets.mp hp.1).1
  have hBA := (mem_countingGoodDeletions.mp hp.2).1
  refine ⟨hmax.subset (hBA hb), ?_⟩
  refine ⟨?_, hmax.sumFree.mono ?_⟩
  · simp [hb]
  · exact insert_subset (hBA hb) sdiff_subset

/-- Within one core fiber, the deleted set determines the original maximal
set: `A = (A \ B) ∪ B`. -/
theorem snd_injective_on_coreFiber (n : ℕ) (S : Finset ℕ) :
    Set.InjOn Prod.snd
      (↑({p ∈ goodDeletionPairs n | deletionCore p = S}) :
        Set (Finset ℕ × Finset ℕ)) := by
  intro p hp q hq hsnd
  rcases p with ⟨A, B⟩
  rcases q with ⟨C, D⟩
  simp only at hsnd
  subst D
  have hpPair : (A, B) ∈ goodDeletionPairs n := (Finset.mem_filter.mp hp).1
  have hqPair : (C, B) ∈ goodDeletionPairs n := (Finset.mem_filter.mp hq).1
  have hpCore : A \ B = S := (Finset.mem_filter.mp hp).2
  have hqCore : C \ B = S := (Finset.mem_filter.mp hq).2
  have hBA : B ⊆ A :=
    (mem_countingGoodDeletions.mp (mem_goodDeletionPairs.mp hpPair).2).1
  have hBC : B ⊆ C :=
    (mem_countingGoodDeletions.mp (mem_goodDeletionPairs.mp hqPair).2).1
  apply Prod.ext
  · rw [← Finset.sdiff_union_of_subset hBA, ← Finset.sdiff_union_of_subset hBC,
      hpCore, hqCore]
  · rfl

/-- Exact lower count: if every large maximal set has at least `L` good
deletions, then there are at least `L` times as many good pairs. -/
theorem mul_card_large_le_card_goodDeletionPairs {n L : ℕ}
    (hgood : ∀ A ∈ largeMaximalSumFreeSets n,
      L ≤ (countingGoodDeletions n A).card) :
    L * (largeMaximalSumFreeSets n).card ≤ (goodDeletionPairs n).card := by
  classical
  have hmaps : Set.MapsTo Prod.fst
      (↑(goodDeletionPairs n) : Set (Finset ℕ × Finset ℕ))
      (↑(largeMaximalSumFreeSets n) : Set (Finset ℕ)) := by
    intro p hp
    rcases p with ⟨A, B⟩
    exact (mem_goodDeletionPairs.mp hp).1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    L * (largeMaximalSumFreeSets n).card =
        ∑ A ∈ largeMaximalSumFreeSets n, L := by
          simp [mul_comm]
    _ ≤ ∑ A ∈ largeMaximalSumFreeSets n,
        #({p ∈ goodDeletionPairs n | p.1 = A}) := by
      apply Finset.sum_le_sum
      intro A hA
      refine (hgood A hA).trans_eq ?_
      apply Finset.card_bij (fun B _ ↦ (A, B))
      · intro B hB
        simp only [Finset.mem_filter, and_true]
        exact mem_goodDeletionPairs.mpr ⟨hA, hB⟩
      · intro B₁ hB₁ B₂ hB₂ heq
        exact Prod.mk.inj heq |>.2
      · intro p hp
        rcases p with ⟨C, B⟩
        have hC : C = A := (Finset.mem_filter.mp hp).2
        subst C
        exact ⟨B, (mem_goodDeletionPairs.mp (Finset.mem_filter.mp hp).1).2, rfl⟩

/-- Exact upper count: if every good core has at most `r` addable points,
then the good-pair incidence set has size at most `f(n) 2^r`. -/
theorem card_goodDeletionPairs_le_sumFreeCount_mul_pow {n r : ℕ}
    (hext : ∀ p ∈ goodDeletionPairs n,
      (extensionCandidates (interval n) (deletionCore p)).card ≤ r) :
    (goodDeletionPairs n).card ≤ sumFreeCount n * 2 ^ r := by
  classical
  have hmaps : Set.MapsTo deletionCore
      (↑(goodDeletionPairs n) : Set (Finset ℕ × Finset ℕ))
      (↑(sumFreeSets n) : Set (Finset ℕ)) := by
    intro p hp
    exact deletionCore_mem_sumFreeSets hp
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    ∑ S ∈ sumFreeSets n, #({p ∈ goodDeletionPairs n | deletionCore p = S})
        ≤ ∑ S ∈ sumFreeSets n, 2 ^ r := by
      apply Finset.sum_le_sum
      intro S hS
      let fiber := {p ∈ goodDeletionPairs n | deletionCore p = S}
      let target := (extensionCandidates (interval n) S).powerset
      by_cases hf : fiber.Nonempty
      · have hcard : fiber.card ≤ target.card := by
          apply Finset.card_le_card_of_injOn Prod.snd
          · intro p hp
            have hpPair : p ∈ goodDeletionPairs n := (Finset.mem_filter.mp hp).1
            have hpCore : deletionCore p = S := (Finset.mem_filter.mp hp).2
            apply Finset.mem_powerset.mpr
            rw [← hpCore]
            simpa only [deletionCore] using
              deletion_subset_extensionCandidates
                (A := p.1) (B := p.2) (by simpa using hpPair)
          · simpa only [fiber] using snd_injective_on_coreFiber n S
        obtain ⟨p, hp⟩ := hf
        have hpPair : p ∈ goodDeletionPairs n := (Finset.mem_filter.mp hp).1
        have hpCore : deletionCore p = S := (Finset.mem_filter.mp hp).2
        calc
          #({p ∈ goodDeletionPairs n | deletionCore p = S}) = fiber.card := rfl
          _ ≤ target.card := hcard
          _ = 2 ^ (extensionCandidates (interval n) S).card :=
            Finset.card_powerset _
          _ ≤ 2 ^ r := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) (by
            simpa only [← hpCore] using hext p hpPair)
      · have hempty : fiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hf
        simp [fiber, hempty]
    _ = sumFreeCount n * 2 ^ r := by
      simp [sumFreeCount]

/-- The combined finite double-counting inequality. -/
theorem double_count_large_maximal {n L r : ℕ}
    (hgood : ∀ A ∈ largeMaximalSumFreeSets n,
      L ≤ (countingGoodDeletions n A).card)
    (hext : ∀ p ∈ goodDeletionPairs n,
      (extensionCandidates (interval n) (deletionCore p)).card ≤ r) :
    L * (largeMaximalSumFreeSets n).card ≤ sumFreeCount n * 2 ^ r :=
  (mul_card_large_le_card_goodDeletionPairs hgood).trans
    (card_goodDeletionPairs_le_sumFreeCount_mul_pow hext)

/-- The concrete finite inequality obtained from the good-deletion lemma.
The left factor grows like
`(2^21)^(n / (10 * (2^21 + 1)))`, while a fixed core has at most
`2^(2n / (2^21 + 1))` possible deleted parts. -/
theorem concrete_large_double_count (n : ℕ)
    (hn : 10 * (deletionDenom + 1) ≤ n) :
    (deletionDenom ^ (n / (10 * (deletionDenom + 1))) / 20) *
        (largeMaximalSumFreeSets n).card ≤
      sumFreeCount n * 2 ^ ((2 * n) / (deletionDenom + 1)) := by
  apply double_count_large_maximal
  · intro A hA
    have hdata := mem_largeMaximalSumFreeSets.mp hA
    have hqA : deletionDenom + 1 ≤ A.card := by
      have hten : 10 * (deletionDenom + 1) ≤ 10 * A.card := hn.trans hdata.2
      omega
    have hfrac : n / (10 * (deletionDenom + 1)) ≤
        A.card / (deletionDenom + 1) := by
      calc
        n / (10 * (deletionDenom + 1)) ≤
            (10 * A.card) / (10 * (deletionDenom + 1)) :=
          Nat.div_le_div_right hdata.2
        _ = A.card / (deletionDenom + 1) := by
          simpa [mul_comm] using
            (Nat.mul_div_mul_left A.card (deletionDenom + 1)
              (by norm_num : 0 < 10))
    have hbase : 1 ≤ deletionDenom := by
      norm_num [deletionDenom]
    have hpow :
        deletionDenom ^ (n / (10 * (deletionDenom + 1))) ≤
          deletionDenom ^ (A.card / (deletionDenom + 1)) :=
      pow_le_pow_right' hbase hfrac
    have hchoose :
        deletionDenom ^ (A.card / (deletionDenom + 1)) ≤
          A.card.choose (A.card / (deletionDenom + 1)) := by
      simpa using pred_pow_div_le_choose A.card (deletionDenom + 1)
        (by omega : 1 ≤ deletionDenom + 1)
    calc
      deletionDenom ^ (n / (10 * (deletionDenom + 1))) / 20 ≤
          A.card.choose (A.card / (deletionDenom + 1)) / 20 :=
        Nat.div_le_div_right (hpow.trans hchoose)
      _ ≤ (goodDeletionsWith (deletionDenom + 1) n A hdata.1).card := by
        simpa [deletionSizeWith] using
          goodDeletionsWith_card_lower (q := deletionDenom + 1) (d := 10)
            hdata.1 (by omega : 0 < deletionDenom + 1) hdata.2 hqA
      _ = (countingGoodDeletions n A).card := by
        rw [countingGoodDeletions_eq n A hdata.1]
  · intro p hp
    rcases p with ⟨A, B⟩
    have hgood := (mem_countingGoodDeletions.mp
      (mem_goodDeletionPairs.mp hp).2).2.2
    apply (Nat.le_div_iff_mul_le (by omega : 0 < deletionDenom + 1)).2
    simpa [deletionCore, mul_comm] using hgood

/-- Power-of-two form of `concrete_large_double_count`.  Dividing by `20`
costs at most five binary digits. -/
theorem concrete_large_double_count_pow (n : ℕ)
    (hn : 10 * (deletionDenom + 1) ≤ n) :
    2 ^ (21 * (n / (10 * (deletionDenom + 1))) - 5) *
        (largeMaximalSumFreeSets n).card ≤
      sumFreeCount n * 2 ^ ((2 * n) / (deletionDenom + 1)) := by
  let e := n / (10 * (deletionDenom + 1))
  have he : 1 ≤ e := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < 10 * (deletionDenom + 1))]
    simpa [e] using hn
  have hfive : 5 ≤ 21 * e := by omega
  have hfactor : 2 ^ (21 * e - 5) ≤ deletionDenom ^ e / 20 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 20)).2
    calc
      2 ^ (21 * e - 5) * 20 ≤ 2 ^ (21 * e - 5) * 32 := by
        exact Nat.mul_le_mul_left _ (by norm_num : 20 ≤ 32)
      _ = 2 ^ (21 * e) := by
        rw [show 32 = 2 ^ 5 by norm_num, ← pow_add]
        congr 1
        omega
      _ = deletionDenom ^ e := by
        simp [deletionDenom, pow_mul]
  calc
    2 ^ (21 * (n / (10 * (deletionDenom + 1))) - 5) *
        (largeMaximalSumFreeSets n).card =
        2 ^ (21 * e - 5) * (largeMaximalSumFreeSets n).card := by rfl
    _ ≤ (deletionDenom ^ e / 20) *
        (largeMaximalSumFreeSets n).card :=
      Nat.mul_le_mul_right _ hfactor
    _ ≤ sumFreeCount n * 2 ^ ((2 * n) / (deletionDenom + 1)) := by
      simpa [e] using concrete_large_double_count n hn

/-- A ready-to-use upper bound after inserting any power-of-two estimate for
the number of all sum-free cores and cancelling the deletion gain. -/
theorem large_card_le_pow_of_sumFreeCount_le (n s : ℕ)
    (hn : 10 * (deletionDenom + 1) ≤ n)
    (hsf : sumFreeCount n ≤ 2 ^ s)
    (hbudget :
      21 * (n / (10 * (deletionDenom + 1))) - 5 ≤
        s + (2 * n) / (deletionDenom + 1)) :
    (largeMaximalSumFreeSets n).card ≤
      2 ^ (s + (2 * n) / (deletionDenom + 1) -
        (21 * (n / (10 * (deletionDenom + 1))) - 5)) := by
  let a := 21 * (n / (10 * (deletionDenom + 1))) - 5
  let b := s + (2 * n) / (deletionDenom + 1)
  have hdc : 2 ^ a * (largeMaximalSumFreeSets n).card ≤ 2 ^ b := by
    calc
      2 ^ a * (largeMaximalSumFreeSets n).card ≤
          sumFreeCount n * 2 ^ ((2 * n) / (deletionDenom + 1)) := by
        simpa [a] using concrete_large_double_count_pow n hn
      _ ≤ 2 ^ s * 2 ^ ((2 * n) / (deletionDenom + 1)) :=
        Nat.mul_le_mul_right _ hsf
      _ = 2 ^ b := by simp [b, pow_add]
  have hb : a ≤ b := by simpa [a, b] using hbudget
  have hfactored :
      2 ^ a * (largeMaximalSumFreeSets n).card ≤ 2 ^ a * 2 ^ (b - a) := by
    simpa [← pow_add, Nat.add_sub_of_le hb] using hdc
  exact Nat.le_of_mul_le_mul_left hfactored (by positivity)

end Erdos877
