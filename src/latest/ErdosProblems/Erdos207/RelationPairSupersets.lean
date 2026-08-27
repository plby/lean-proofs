/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UniformSupersetCounts

/-! # Supersets of symmetric collision pairs -/

namespace Erdos207

open Finset

noncomputable section

def relationPairFamily
    {I : Type*} [Fintype I] [DecidableEq I] (R : I → I → Prop) : Finset (Finset I) := by
  classical
  exact univ.biUnion (fun i ↦ (univ.filter (fun j ↦ i ≠ j ∧ R i j)).image (fun j ↦ {i, j}))

theorem mem_relationPairFamily_iff
    {I : Type*} [Fintype I] [DecidableEq I] (R : I → I → Prop) (E : Finset I) :
    E ∈ relationPairFamily R ↔ ∃ i j, i ≠ j ∧ R i j ∧ E = {i, j} := by
  classical
  simp only [relationPairFamily, mem_biUnion, mem_univ, true_and, mem_image, mem_filter]
  constructor
  · rintro ⟨i, j, ⟨hne, hR⟩, heq⟩
    exact ⟨i, j, hne, hR, heq.symm⟩
  · rintro ⟨i, j, hne, hR, heq⟩
    exact ⟨i, j, ⟨hne, hR⟩, heq.symm⟩

theorem relationPairFamily_uniform
    {I : Type*} [Fintype I] [DecidableEq I] (R : I → I → Prop) :
    ∀ E ∈ relationPairFamily R, E.card = 2 := by
  intro E hE
  obtain ⟨i, j, hne, _hR, rfl⟩ := (mem_relationPairFamily_iff R E).mp hE
  simp [hne]

theorem relationPairFamily_degree_le
    {I : Type*} [Fintype I] [DecidableEq I] (R : I → I → Prop)
    [DecidableRel R]
    (hsym : ∀ ⦃i j⦄, R i j → R j i) (v : I) :
    finiteHypergraphDegree (relationPairFamily R) v ≤
      (univ.filter (fun w : I ↦ v ≠ w ∧ R v w)).card := by
  classical
  have hsub : ((relationPairFamily R).filter (fun E ↦ v ∈ E)) ⊆
      (univ.filter (fun w : I ↦ v ≠ w ∧ R v w)).image (fun w ↦ {v, w}) := by
    intro E hE
    have hm := mem_filter.mp hE
    obtain ⟨i, j, hne, hR, rfl⟩ := (mem_relationPairFamily_iff R E).mp hm.1
    rcases mem_insert.mp hm.2 with hvi | hvj
    · subst i
      exact mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ j, hne, hR⟩, rfl⟩
    · have hvj' : v = j := mem_singleton.mp hvj
      subst j
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, hne.symm, hsym hR⟩, pair_comm _ _⟩
  exact (card_le_card hsub).trans card_image_le

theorem relationPairSupersets_max_degree_le
    {I : Type*} [Fintype I] [DecidableEq I] (R : I → I → Prop)
    [DecidableRel R]
    (hsym : ∀ ⦃i j⦄, R i j → R j i) (B k : ℕ) (hk : 2 ≤ k)
    (hdegree : ∀ v, (univ.filter (fun w : I ↦ v ≠ w ∧ R v w)).card ≤ B) :
    finiteHypergraphMaxDegree (uniformSupersets k (relationPairFamily R)) ≤
      2 * B * (Fintype.card I) ^ (k - 2) := by
  have hmax : finiteHypergraphMaxDegree (relationPairFamily R) ≤ B :=
    (finiteHypergraphMaxDegree_le_iff _ _).mpr (fun v ↦ (relationPairFamily_degree_le R hsym v).trans (hdegree v))
  exact (uniformSupersets_max_degree_le_of_le k 2 (relationPairFamily R) (by omega) hk
    (relationPairFamily_uniform R)).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hmax))

end

end Erdos207
