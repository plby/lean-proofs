/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteHypergraphDegrees
import Mathlib.Tactic.Ring

/-! # The signed five-set correction for fractional triangle regularization -/

namespace Erdos207

open Finset

noncomputable section

def triangleEdgeCorrection {V : Type*} [DecidableEq V] (P T : Finset V) : ℝ :=
  if (T ∩ P).card = 1 then -(1 / 6) else 1 / 3

theorem triangleEdgeCorrection_abs_le
    {V : Type*} [DecidableEq V] (P T : Finset V) : |triangleEdgeCorrection P T| ≤ (1 / 3 : ℝ) := by
  unfold triangleEdgeCorrection
  split_ifs <;> norm_num

theorem triangleEdgeCorrection_insert
    {V : Type*} [DecidableEq V] (P Q : Finset V) (v : V) (hv : v ∉ Q) :
    triangleEdgeCorrection P (insert v Q) =
      if v ∈ P then (if (Q ∩ P).card + 1 = 1 then -(1 / 6 : ℝ) else 1 / 3)
      else (if (Q ∩ P).card = 1 then -(1 / 6 : ℝ) else 1 / 3) := by
  unfold triangleEdgeCorrection
  by_cases hP : v ∈ P
  · rw [if_pos hP]
    have heq : insert v Q ∩ P = insert v (Q ∩ P) := by ext x; simp; aesop
    rw [heq, card_insert_of_notMem (fun h ↦ hv (mem_inter.mp h).1)]
  · rw [if_neg hP]
    have heq : insert v Q ∩ P = Q ∩ P := by ext x; simp; aesop
    rw [heq]

theorem fiveSet_pair_class_card
    {V : Type*} [DecidableEq V] (J P Q : Finset V)
    (hJ : J.card = 5) (hP : P.card = 2) (hQ : Q.card = 2) (hPJ : P ⊆ J) (hQJ : Q ⊆ J) :
    ((J \ Q).filter (fun v ↦ v ∈ P)).card = 2 - (Q ∩ P).card ∧
      ((J \ Q).filter (fun v ↦ v ∉ P)).card = 1 + (Q ∩ P).card := by
  have hin : (J \ Q).filter (fun v ↦ v ∈ P) = P \ Q := by
    ext v
    simp only [mem_filter, mem_sdiff]
    constructor
    · exact fun h ↦ ⟨h.2, h.1.2⟩
    · exact fun h ↦ ⟨⟨hPJ h.1, h.2⟩, h.1⟩
  have hr : (Q ∩ P).card ≤ 2 := (card_le_card inter_subset_left).trans_eq hQ
  have hc : (J \ Q).card = 3 := by rw [card_sdiff_of_subset hQJ, hJ, hQ]
  have hfirst : ((J \ Q).filter (fun v ↦ v ∈ P)).card = 2 - (Q ∩ P).card := by
    rw [hin, card_sdiff, hP, inter_comm]
  refine ⟨hfirst, ?_⟩
  have hs := card_filter_add_card_filter_not (s := J \ Q) (p := fun v ↦ v ∈ P)
  rw [hc, hfirst] at hs
  omega

theorem fiveSet_triangleEdgeCorrection_sum
    {V : Type*} [DecidableEq V] (J P Q : Finset V)
    (hJ : J.card = 5) (hP : P.card = 2) (hQ : Q.card = 2) (hPJ : P ⊆ J) (hQJ : Q ⊆ J) :
    (∑ v ∈ J \ Q, triangleEdgeCorrection P (insert v Q)) = if P = Q then (1 : ℝ) else 0 := by
  have hclasses := fiveSet_pair_class_card J P Q hJ hP hQ hPJ hQJ
  have hsum : (∑ v ∈ J \ Q, triangleEdgeCorrection P (insert v Q)) =
      ∑ v ∈ J \ Q, if v ∈ P then
        (if (Q ∩ P).card + 1 = 1 then -(1 / 6 : ℝ) else 1 / 3)
      else (if (Q ∩ P).card = 1 then -(1 / 6 : ℝ) else 1 / 3) :=
    sum_congr rfl (fun v hv ↦ triangleEdgeCorrection_insert P Q v (mem_sdiff.mp hv).2)
  rw [hsum, sum_ite]
  simp only [sum_const, nsmul_eq_mul, hclasses.1, hclasses.2]
  have hr : (Q ∩ P).card ≤ 2 := (card_le_card inter_subset_left).trans_eq hQ
  have hcase : (Q ∩ P).card = 0 ∨ (Q ∩ P).card = 1 ∨ (Q ∩ P).card = 2 := by omega
  rcases hcase with hr0 | hr1 | hr2
  · have hne : P ≠ Q := by intro heq; subst P; simp [hQ] at hr0
    norm_num [hr0, hne]
  · have hne : P ≠ Q := by intro heq; subst P; simp [hQ] at hr1
    norm_num [hr1, hne]
  · have hQP : Q ⊆ P := by
      have heq : Q ∩ P = Q := eq_of_subset_of_card_le inter_subset_left (by rw [hQ, hr2])
      rw [← heq]
      exact inter_subset_right
    have heq : P = Q := (eq_of_subset_of_card_le hQP (by rw [hP, hQ])).symm
    norm_num [heq, hQ]

theorem sum_trianglesThrough_pair
    {V : Type*} [DecidableEq V] (J Q : Finset V) (hQ : Q.card = 2) (hQJ : Q ⊆ J)
    (f : Finset V → ℝ) :
    (∑ T ∈ (J.powersetCard 3).filter (Q ⊆ ·), f T) =
      ∑ v ∈ J \ Q, f (insert v Q) := by
  symm
  apply sum_bij (fun v _ ↦ insert v Q)
  · intro v hv
    have hm := mem_sdiff.mp hv
    exact mem_filter.mpr ⟨mem_powersetCard.mpr
      ⟨insert_subset hm.1 hQJ, by rw [card_insert_of_notMem hm.2, hQ]⟩,
      subset_insert _ _⟩
  · intro v hv w hw heq
    have hm : v ∈ insert w Q := heq ▸ mem_insert_self v Q
    exact (mem_insert.mp hm).resolve_right (mem_sdiff.mp hv).2
  · intro T hT
    have hm := mem_filter.mp hT
    have hc : (T \ Q).card = 1 := by
      rw [card_sdiff_of_subset hm.2, (mem_powersetCard.mp hm.1).2, hQ]
    obtain ⟨v, hv⟩ := card_eq_one.mp hc
    have hvT : v ∈ T \ Q := hv.symm ▸ mem_singleton_self v
    refine ⟨v, mem_sdiff.mpr ⟨(mem_powersetCard.mp hm.1).1
      (mem_sdiff.mp hvT).1, (mem_sdiff.mp hvT).2⟩, ?_⟩
    have hu := sdiff_union_of_subset hm.2
    simpa only [hv, singleton_union] using hu
  · intro v hv
    rfl

def fiveSetEdgeCorrection {V : Type*} [DecidableEq V]
    (P J T : Finset V) : ℝ := if T ⊆ J then triangleEdgeCorrection P T else 0

theorem fiveSetEdgeCorrection_abs_le
    {V : Type*} [DecidableEq V] (P J T : Finset V) :
    |fiveSetEdgeCorrection P J T| ≤ if T ⊆ J then (1 / 3 : ℝ) else 0 := by
  unfold fiveSetEdgeCorrection
  split_ifs
  · exact triangleEdgeCorrection_abs_le P T
  · simp

theorem fiveSetEdgeCorrection_delta
    {V : Type*} [DecidableEq V] (A : Finset (Finset V)) (J P Q : Finset V)
    (hA : ∀ T ∈ A, T.card = 3) (hJ : J.card = 5)
    (hJA : J.powersetCard 3 ⊆ A) (hP : P.card = 2) (hQ : Q.card = 2) (hPJ : P ⊆ J) :
    (∑ T ∈ A.filter (Q ⊆ ·), fiveSetEdgeCorrection P J T) =
      if P = Q then (1 : ℝ) else 0 := by
  have hfilter : (A.filter (Q ⊆ ·)).filter (· ⊆ J) =
      (J.powersetCard 3).filter (Q ⊆ ·) := by
    ext T
    simp only [mem_filter, mem_powersetCard]
    constructor
    · exact fun h ↦ ⟨⟨h.2, hA T h.1.1⟩, h.1.2⟩
    · exact fun h ↦ ⟨⟨hJA (mem_powersetCard.mpr h.1), h.2⟩, h.1.1⟩
  unfold fiveSetEdgeCorrection
  rw [← sum_filter, hfilter]
  by_cases hQJ : Q ⊆ J
  · rw [sum_trianglesThrough_pair J Q hQ hQJ]
    exact fiveSet_triangleEdgeCorrection_sum J P Q hJ hP hQ hPJ hQJ
  · have hempty : (J.powersetCard 3).filter (Q ⊆ ·) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro T hT
      have hm := mem_filter.mp hT
      exact hQJ (hm.2.trans (mem_powersetCard.mp hm.1).1)
    have hne : P ≠ Q := by intro heq; exact hQJ (heq ▸ hPJ)
    simp [hempty, hne]

end

end Erdos207
