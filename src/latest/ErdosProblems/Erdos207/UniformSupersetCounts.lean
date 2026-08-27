/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteHypergraphDegrees
import Mathlib.Data.Nat.Choose.Bounds

/-! # Rooted counts for supersets of smaller forbidden configurations -/

namespace Erdos207

open Finset

noncomputable section

def uniformSupersets
    {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ) (F : Finset (Finset I)) : Finset (Finset I) := by
  classical
  exact (univ.powersetCard k).filter (fun E ↦ ∃ C ∈ F, C ⊆ E)

theorem mem_uniformSupersets_iff
    {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ) (F : Finset (Finset I)) (E : Finset I) :
    E ∈ uniformSupersets k F ↔ E.card = k ∧ ∃ C ∈ F, C ⊆ E := by
  classical
  simp [uniformSupersets]

theorem card_uniform_completions_le
    {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ) (Q : Finset I) (hQ : Q.card ≤ k) :
    ((univ.powersetCard k).filter (Q ⊆ ·)).card ≤ (Fintype.card I) ^ (k - Q.card) := by
  rw [card_filter_powersetCard_subset Q univ k (subset_univ Q) hQ, card_univ]
  exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)

theorem finiteHypergraph_card_le_card_mul_max_degree
    {I : Type*} [Fintype I] [DecidableEq I] (F : Finset (Finset I))
    (hne : ∀ C ∈ F, C.Nonempty) : F.card ≤ Fintype.card I * finiteHypergraphMaxDegree F := by
  classical
  have hcover : F ⊆ univ.biUnion (fun v : I ↦ F.filter (fun C ↦ v ∈ C)) := by
    intro C hC
    obtain ⟨v, hv⟩ := hne C hC
    exact mem_biUnion.mpr ⟨v, mem_univ v, mem_filter.mpr ⟨hC, hv⟩⟩
  calc
    _ ≤ (univ.biUnion (fun v : I ↦ F.filter (fun C ↦ v ∈ C))).card := card_le_card hcover
    _ ≤ ∑ v : I, (F.filter (fun C ↦ v ∈ C)).card := card_biUnion_le
    _ ≤ ∑ _v : I, finiteHypergraphMaxDegree F := sum_le_sum (fun v _ ↦ finiteHypergraphDegree_le_max F v)
    _ = _ := by simp

theorem uniformSupersets_degree_le_sum
    {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ) (F : Finset (Finset I)) (v : I) :
    finiteHypergraphDegree (uniformSupersets k F) v ≤
      ∑ C ∈ F, ((univ.powersetCard k).filter (insert v C ⊆ ·)).card := by
  classical
  have hcover : ((uniformSupersets k F).filter (fun E ↦ v ∈ E)) ⊆
      F.biUnion (fun C ↦ (univ.powersetCard k).filter (insert v C ⊆ ·)) := by
    intro E hE
    have hm := mem_filter.mp hE
    obtain ⟨hcard, C, hC, hCE⟩ := (mem_uniformSupersets_iff k F E).mp hm.1
    exact mem_biUnion.mpr ⟨C, hC, mem_filter.mpr
      ⟨mem_powersetCard.mpr ⟨subset_univ E, hcard⟩, insert_subset hm.2 hCE⟩⟩
  exact (card_le_card hcover).trans card_biUnion_le

theorem uniformSupersets_degree_le
    {I : Type*} [Fintype I] [DecidableEq I] (k s : ℕ) (F : Finset (Finset I)) (v : I)
    (hsk : s < k) (huniform : ∀ C ∈ F, C.card = s) :
    finiteHypergraphDegree (uniformSupersets k F) v ≤
      finiteHypergraphDegree F v * (Fintype.card I) ^ (k - s) +
      F.card * (Fintype.card I) ^ (k - s - 1) := by
  classical
  apply (uniformSupersets_degree_le_sum k F v).trans
  calc
    _ ≤ ∑ C ∈ F, ((if v ∈ C then (Fintype.card I) ^ (k - s) else 0) +
        (Fintype.card I) ^ (k - s - 1)) := by
      apply sum_le_sum
      intro C hC
      by_cases hv : v ∈ C
      · rw [if_pos hv, insert_eq_of_mem hv]
        have hb : ((univ.powersetCard k).filter (C ⊆ ·)).card ≤ (Fintype.card I) ^ (k - s) := by
          simpa only [huniform C hC] using
            card_uniform_completions_le k C (by rw [huniform C hC]; omega)
        exact hb.trans (Nat.le_add_right _ _)
      · rw [if_neg hv, zero_add]
        have hcard : (insert v C).card = s + 1 := by rw [card_insert_of_notMem hv, huniform C hC]
        have h := card_uniform_completions_le k (insert v C) (by rw [hcard]; omega)
        simpa only [hcard, Nat.sub_add_eq] using h
    _ = _ := by
      rw [sum_add_distrib, ← sum_filter]
      simp [finiteHypergraphDegree]

theorem uniformSupersets_max_degree_le
    {I : Type*} [Fintype I] [DecidableEq I] (k s : ℕ) (F : Finset (Finset I))
    (hs : 1 ≤ s) (hsk : s < k) (huniform : ∀ C ∈ F, C.card = s) :
    finiteHypergraphMaxDegree (uniformSupersets k F) ≤
      2 * finiteHypergraphMaxDegree F * (Fintype.card I) ^ (k - s) := by
  have hcard : F.card ≤ Fintype.card I * finiteHypergraphMaxDegree F :=
    finiteHypergraph_card_le_card_mul_max_degree F (fun C hC ↦ card_pos.mp (by rw [huniform C hC]; omega))
  apply (finiteHypergraphMaxDegree_le_iff _ _).mpr
  intro v
  apply (uniformSupersets_degree_le k s F v hsk huniform).trans
  calc
    _ ≤ finiteHypergraphMaxDegree F * (Fintype.card I) ^ (k - s) +
        (Fintype.card I * finiteHypergraphMaxDegree F) * (Fintype.card I) ^ (k - s - 1) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ (finiteHypergraphDegree_le_max F v))
        (Nat.mul_le_mul_right _ hcard)
    _ = _ := by
      have he : k - s = (k - s - 1) + 1 := by omega
      conv_rhs => rw [he, pow_succ]
      conv_lhs => lhs; rw [he, pow_succ]
      ring

theorem uniformSupersets_self_eq
    {I : Type*} [Fintype I] [DecidableEq I] (s : ℕ) (F : Finset (Finset I))
    (huniform : ∀ C ∈ F, C.card = s) : uniformSupersets s F = F := by
  ext E
  rw [mem_uniformSupersets_iff]
  constructor
  · rintro ⟨hE, C, hC, hCE⟩
    have heq : C = E := eq_of_subset_of_card_le hCE (by rw [huniform C hC, hE])
    exact heq ▸ hC
  · intro hE
    exact ⟨huniform E hE, E, hE, Subset.rfl⟩

theorem uniformSupersets_max_degree_le_of_le
    {I : Type*} [Fintype I] [DecidableEq I] (k s : ℕ) (F : Finset (Finset I))
    (hs : 1 ≤ s) (hsk : s ≤ k) (huniform : ∀ C ∈ F, C.card = s) :
    finiteHypergraphMaxDegree (uniformSupersets k F) ≤
      2 * finiteHypergraphMaxDegree F * (Fintype.card I) ^ (k - s) := by
  rcases hsk.eq_or_lt with heq | hlt
  · subst k
    rw [uniformSupersets_self_eq s F huniform, Nat.sub_self, pow_zero, mul_one]
    omega
  · exact uniformSupersets_max_degree_le k s F hs hlt huniform

end

end Erdos207
