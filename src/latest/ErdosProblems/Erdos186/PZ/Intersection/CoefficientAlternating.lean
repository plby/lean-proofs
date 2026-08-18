/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib

/-!
# Coefficient-balanced alternating partitions

Sorting nonnegative weights in decreasing order and assigning consecutive
terms alternately gives two cardinal-balanced parts whose total weights
differ by at most the largest weight.  This is the actual partition used in
the Pham--Zakharov intersection argument.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

namespace List

/-- Entries in even positions, defined pairwise to simplify induction. -/
def alternatingLeft {α : Type*} : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _y :: tail => x :: alternatingLeft tail

/-- Entries in odd positions, defined pairwise to simplify induction. -/
def alternatingRight {α : Type*} : List α → List α
  | [] => []
  | [_x] => []
  | _x :: y :: tail => y :: alternatingRight tail

@[simp] theorem alternatingLeft_nil {α : Type*} :
    alternatingLeft ([] : List α) = [] := rfl

@[simp] theorem alternatingRight_nil {α : Type*} :
    alternatingRight ([] : List α) = [] := rfl

@[simp] theorem alternatingLeft_singleton {α : Type*} (x : α) :
    alternatingLeft [x] = [x] := rfl

@[simp] theorem alternatingRight_singleton {α : Type*} (x : α) :
    alternatingRight [x] = [] := rfl

@[simp] theorem alternatingLeft_pair {α : Type*} (x y : α) (tail : List α) :
    alternatingLeft (x :: y :: tail) = x :: alternatingLeft tail := rfl

@[simp] theorem alternatingRight_pair {α : Type*} (x y : α) (tail : List α) :
    alternatingRight (x :: y :: tail) = y :: alternatingRight tail := rfl

@[simp] theorem alternatingLeft_map {α β : Type*} (f : α → β) :
    ∀ l : List α,
      alternatingLeft (l.map f) = (alternatingLeft l).map f
  | [] => by simp
  | [x] => by simp
  | x :: y :: tail => by
      simp only [List.map_cons, alternatingLeft_pair, alternatingLeft_map f tail]

@[simp] theorem alternatingRight_map {α β : Type*} (f : α → β) :
    ∀ l : List α,
      alternatingRight (l.map f) = (alternatingRight l).map f
  | [] => by simp
  | [x] => by simp
  | x :: y :: tail => by
      simp only [List.map_cons, alternatingRight_pair, alternatingRight_map f tail]

theorem alternatingLeft_append_alternatingRight_perm {α : Type*} :
    ∀ l : List α,
      List.Perm (alternatingLeft l ++ alternatingRight l) l
  | [] => by simp
  | [x] => by simp
  | x :: y :: tail => by
      apply List.Perm.cons x
      exact List.perm_middle.trans
        ((alternatingLeft_append_alternatingRight_perm tail).cons y)
theorem alternatingLeft_length {α : Type*} : ∀ l : List α,
    (alternatingLeft l).length = (l.length + 1) / 2
  | [] => by simp
  | [x] => by simp
  | x :: y :: tail => by
      simp only [alternatingLeft_pair, List.length_cons,
        alternatingLeft_length tail]
      omega

theorem alternatingRight_length {α : Type*} : ∀ l : List α,
    (alternatingRight l).length = l.length / 2
  | [] => by simp
  | [x] => by simp
  | x :: y :: tail => by
      simp only [alternatingRight_pair, List.length_cons,
        alternatingRight_length tail]
      omega

theorem alternatingLeft_disjoint_alternatingRight_of_nodup
    {α : Type*} {l : List α} (hl : l.Nodup) :
    List.Disjoint (alternatingLeft l) (alternatingRight l) := by
  apply List.Nodup.disjoint
  exact (alternatingLeft_append_alternatingRight_perm l).nodup_iff.mpr hl

theorem sum_alternatingLeft_sub_sum_alternatingRight :
    ∀ l : List ℝ,
      (alternatingLeft l).sum - (alternatingRight l).sum =
        l.alternatingSum
  | [] => by simp [List.alternatingSum]
  | [x] => by simp [List.alternatingSum]
  | x :: y :: tail => by
      rw [alternatingLeft_pair, alternatingRight_pair, List.sum_cons, List.sum_cons]
      calc
        x + (alternatingLeft tail).sum - (y + (alternatingRight tail).sum) =
            x - y + ((alternatingLeft tail).sum - (alternatingRight tail).sum) := by ring
        _ = x - y + tail.alternatingSum := by
          rw [sum_alternatingLeft_sub_sum_alternatingRight tail]
        _ = (x :: y :: tail).alternatingSum := by
          simp only [List.alternatingSum]
          ring

/-- The alternating sum of a decreasing nonnegative list lies between zero
and its first term. -/
theorem alternatingSum_nonneg_le_head :
    ∀ {x : ℝ} {tail : List ℝ},
      (x :: tail).Pairwise (fun a b ↦ b ≤ a) →
      (∀ z ∈ x :: tail, 0 ≤ z) →
      0 ≤ (x :: tail).alternatingSum ∧
        (x :: tail).alternatingSum ≤ x
  | x, [], _hsorted, hnonneg => by
      simpa [List.alternatingSum] using hnonneg x (by simp)
  | x, y :: tail, hsorted, hnonneg => by
      have hxy : y ≤ x := (List.pairwise_cons.mp hsorted).1 y (by simp)
      have hsortedTail : (y :: tail).Pairwise (fun a b ↦ b ≤ a) :=
        (List.pairwise_cons.mp hsorted).2
      have hnonnegY : 0 ≤ y := hnonneg y (by simp)
      cases tail with
      | nil =>
          simp only [List.alternatingSum, add_zero]
          constructor <;> linarith
      | cons z zs =>
          have hsortedRest : (z :: zs).Pairwise (fun a b ↦ b ≤ a) :=
            (List.pairwise_cons.mp hsortedTail).2
          have hyz : z ≤ y :=
            (List.pairwise_cons.mp hsortedTail).1 z (by simp)
          have hnonnegRest : ∀ u ∈ z :: zs, 0 ≤ u := by
            intro u hu
            exact hnonneg u (by simp [hu])
          have ih := alternatingSum_nonneg_le_head hsortedRest hnonnegRest
          simp only [List.alternatingSum]
          constructor <;> linarith

end List

/-- A decreasing alternating split of `S \ {a}` has balanced cardinalities
and its two coefficient masses differ by at most the uniform cap. -/
theorem exists_coefficientBalanced_partition_erase
    {α : Type*} [DecidableEq α] (S : Finset α) (a : α) (ha : a ∈ S)
    (weight : α → ℝ) (cap : ℝ)
    (hnonneg : ∀ x ∈ S, 0 ≤ weight x)
    (hcap : ∀ x ∈ S, weight x ≤ cap) :
    ∃ A₁ A₂ : Finset α,
      A₁ ∪ A₂ = S.erase a ∧
      Disjoint A₁ A₂ ∧
      A₁.card = ((S.erase a).card + 1) / 2 ∧
      A₂.card = (S.erase a).card / 2 ∧
      |(∑ x ∈ A₁, weight x) - ∑ x ∈ A₂, weight x| ≤ cap := by
  classical
  let T := S.erase a
  let l := T.toList.mergeSort (fun x y ↦ decide (weight y ≤ weight x))
  let left := List.alternatingLeft l
  let right := List.alternatingRight l
  let A₁ := left.toFinset
  let A₂ := right.toFinset
  have hlPerm : l.Perm T.toList := by
    dsimp only [l]
    exact List.mergeSort_perm _ _
  have hlNodup : l.Nodup := by
    exact hlPerm.nodup_iff.mpr T.nodup_toList
  have hsortedL : l.Pairwise (fun x y ↦ weight y ≤ weight x) := by
    dsimp only [l]
    have h := List.pairwise_mergeSort
      (le := fun x y ↦ decide (weight y ≤ weight x))
      (fun _x _y _z hxy hyz ↦ by
        simp only [decide_eq_true_eq] at hxy hyz ⊢
        exact hyz.trans hxy)
      (fun x y ↦ by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total (weight y) (weight x)) T.toList
    simpa only [decide_eq_true_eq] using h
  have hleftNodup : left.Nodup := by
    have hp := List.alternatingLeft_append_alternatingRight_perm l
    exact (hp.nodup_iff.mpr hlNodup).sublist
      (List.sublist_append_left left right)
  have hrightNodup : right.Nodup := by
    have hp := List.alternatingLeft_append_alternatingRight_perm l
    exact (hp.nodup_iff.mpr hlNodup).sublist
      (List.sublist_append_right left right)
  have hunion : A₁ ∪ A₂ = T := by
    have hp := List.alternatingLeft_append_alternatingRight_perm l
    ext x
    change x ∈ left.toFinset ∪ right.toFinset ↔ x ∈ T
    simp only [Finset.mem_union, List.mem_toFinset, ← List.mem_append]
    rw [hp.mem_iff, hlPerm.mem_iff, Finset.mem_toList]
  have hdisjoint : Disjoint A₁ A₂ := by
    change Disjoint left.toFinset right.toFinset
    rw [List.disjoint_toFinset_iff_disjoint]
    exact List.alternatingLeft_disjoint_alternatingRight_of_nodup hlNodup
  have hcard₁ : A₁.card = (T.card + 1) / 2 := by
    change left.toFinset.card = (T.card + 1) / 2
    rw [List.toFinset_card_of_nodup hleftNodup,
      show left = List.alternatingLeft l from rfl,
      List.alternatingLeft_length, hlPerm.length_eq, Finset.length_toList]
  have hcard₂ : A₂.card = T.card / 2 := by
    change right.toFinset.card = T.card / 2
    rw [List.toFinset_card_of_nodup hrightNodup,
      show right = List.alternatingRight l from rfl,
      List.alternatingRight_length, hlPerm.length_eq, Finset.length_toList]
  have hmass : |(∑ x ∈ A₁, weight x) - ∑ x ∈ A₂, weight x| ≤ cap := by
    have hsumEq :
        (∑ x ∈ A₁, weight x) - ∑ x ∈ A₂, weight x =
          (l.map weight).alternatingSum := by
      change (∑ x ∈ left.toFinset, weight x) -
          ∑ x ∈ right.toFinset, weight x = _
      rw [List.sum_toFinset weight hleftNodup,
        List.sum_toFinset weight hrightNodup]
      rw [← List.alternatingLeft_map weight l,
        ← List.alternatingRight_map weight l,
        List.sum_alternatingLeft_sub_sum_alternatingRight]
    rw [hsumEq]
    cases hl : l with
    | nil =>
        have hacap : 0 ≤ cap := (hnonneg a ha).trans (hcap a ha)
        simpa [hl, List.alternatingSum] using hacap
    | cons x tail =>
        have hsorted : (l.map weight).Pairwise (fun u v ↦ v ≤ u) := by
          rw [List.pairwise_map]
          exact hsortedL
        have hnonnegMap : ∀ z ∈ l.map weight, 0 ≤ z := by
          intro z hz
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
          apply hnonneg y
          have hyT : y ∈ T := by
            exact Finset.mem_toList.mp (hlPerm.mem_iff.mp hy)
          exact Finset.mem_of_mem_erase hyT
        have hsorted' : ((x :: tail).map weight).Pairwise (fun u v ↦ v ≤ u) := by
          simpa only [hl] using hsorted
        have hnonnegMap' : ∀ z ∈ (x :: tail).map weight, 0 ≤ z := by
          simpa only [hl] using hnonnegMap
        have hb := List.alternatingSum_nonneg_le_head hsorted' hnonnegMap'
        have hxT : x ∈ T := by
          have : x ∈ l := by simp [hl]
          exact Finset.mem_toList.mp (hlPerm.mem_iff.mp this)
        have hxcap : weight x ≤ cap := hcap x (Finset.mem_of_mem_erase hxT)
        change |(weight x :: tail.map weight).alternatingSum| ≤ cap
        rw [abs_of_nonneg hb.1]
        exact hb.2.trans hxcap
  exact ⟨A₁, A₂, by simpa only [T] using hunion, hdisjoint,
    by simpa only [T] using hcard₁, by simpa only [T] using hcard₂, hmass⟩

end

end Erdos186.PZ.Intersection
