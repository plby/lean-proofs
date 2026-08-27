/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.Basic
import ErdosProblems.Erdos207.UniformSupersetCounts

/-! # Vertex-local counts for collisions between available triangles -/

namespace Erdos207

open Finset

noncomputable section

theorem card_auxiliary_triangles_le
    {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
    (e : I ↪ TripleOn V) (U : Finset V) (hsupport : ∀ i, (e i).1 ⊆ U) :
    Fintype.card I ≤ U.card ^ 3 := by
  have hcount : (univ : Finset I).card ≤ (U.powersetCard 3).card := by
    apply card_le_card_of_injOn (fun i : I ↦ (e i).1)
    · intro i _hi
      exact mem_powersetCard.mpr ⟨hsupport i, (e i).2⟩
    · intro i _hi j _hj heq
      exact e.injective (Subtype.ext heq)
  rw [card_univ, card_powersetCard] at hcount
  exact hcount.trans (Nat.choose_le_pow _ _)

theorem card_auxiliary_triangles_containing_le
    {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
    (e : I ↪ TripleOn V) (U : Finset V) (hsupport : ∀ i, (e i).1 ⊆ U) (v : V) :
    (univ.filter (fun i : I ↦ v ∈ (e i).1)).card ≤ U.card ^ 2 := by
  have hcount : (univ.filter (fun i : I ↦ v ∈ (e i).1)).card ≤ (U.powersetCard 2).card := by
    apply card_le_card_of_injOn (fun i : I ↦ (e i).1.erase v)
    · intro i hi
      have hv := (mem_filter.mp hi).2
      exact mem_powersetCard.mpr ⟨(erase_subset v (e i).1).trans (hsupport i), by rw [card_erase_of_mem hv, (e i).2]⟩
    · intro i hi j hj heq
      change (e i).1.erase v = (e j).1.erase v at heq
      apply e.injective
      apply Subtype.ext
      have hvi := (mem_filter.mp hi).2
      have hvj := (mem_filter.mp hj).2
      calc
        (e i).1 = insert v ((e i).1.erase v) := (insert_erase hvi).symm
        _ = insert v ((e j).1.erase v) := by rw [heq]
        _ = (e j).1 := insert_erase hvj
  rw [card_powersetCard] at hcount
  exact hcount.trans (Nat.choose_le_pow _ _)

abbrev auxiliaryTriangleCollision
    {V I : Type*} [DecidableEq V] (e : I ↪ TripleOn V) (i j : I) : Prop :=
  ¬ Disjoint (e i).1 (e j).1

theorem auxiliaryTriangleCollision_symmetric
    {V I : Type*} [DecidableEq V] (e : I ↪ TripleOn V) :
    ∀ ⦃i j⦄, auxiliaryTriangleCollision e i j → auxiliaryTriangleCollision e j i := by
  intro i j h
  exact fun hd ↦ h hd.symm

theorem card_auxiliary_collision_neighbors_le
    {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
    (e : I ↪ TripleOn V) (U : Finset V) (hsupport : ∀ i, (e i).1 ⊆ U) (i : I) :
    (univ.filter (fun j : I ↦ i ≠ j ∧ auxiliaryTriangleCollision e i j)).card ≤ 3 * U.card ^ 2 := by
  classical
  have hcover : (univ.filter (fun j : I ↦ i ≠ j ∧ auxiliaryTriangleCollision e i j)) ⊆
      (e i).1.biUnion (fun v ↦ univ.filter (fun j : I ↦ v ∈ (e j).1)) := by
    intro j hj
    obtain ⟨v, hvi, hvj⟩ := not_disjoint_iff.mp (mem_filter.mp hj).2.2
    exact mem_biUnion.mpr ⟨v, hvi, mem_filter.mpr ⟨mem_univ j, hvj⟩⟩
  calc
    _ ≤ ((e i).1.biUnion (fun v ↦ univ.filter (fun j : I ↦ v ∈ (e j).1))).card := card_le_card hcover
    _ ≤ ∑ v ∈ (e i).1, (univ.filter (fun j : I ↦ v ∈ (e j).1)).card := card_biUnion_le
    _ ≤ ∑ _v ∈ (e i).1, U.card ^ 2 := sum_le_sum (fun v _ ↦ card_auxiliary_triangles_containing_le e U hsupport v)
    _ = _ := by simp [(e i).2]

end

end Erdos207
