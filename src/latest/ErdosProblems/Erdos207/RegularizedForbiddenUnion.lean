/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRegularizationOrderData
import ErdosProblems.Erdos207.MinimalForbiddenFamily

/-! # The decoded regularized constraints are a minimal, bounded-order packing family -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def regularizedForbiddenUnion
    {V I : Type*} [DecidableEq V] [DecidableEq I]
    (e : I ↪ TripleOn V) (q : ℕ) (Lstar : ℕ → Finset (Finset I)) : ForbiddenFamilyOn V :=
  ((Icc 4 q).biUnion Lstar).image (Finset.map e)

theorem regularized_order_union_eq_of_subset
    {I : Type*} [DecidableEq I] (q : ℕ) (Lstar : ℕ → Finset (Finset I))
    (huniform : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, E.card = j - 2)
    (havoid : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, ∀ C ∈ (Ico 4 j).biUnion Lstar, ¬ C ⊆ E)
    {C E : Finset I} (hC : C ∈ (Icc 4 q).biUnion Lstar) (hE : E ∈ (Icc 4 q).biUnion Lstar)
    (hCE : C ⊆ E) : C = E := by
  obtain ⟨i, hi, hCi⟩ := mem_biUnion.mp hC
  obtain ⟨j, hj, hEj⟩ := mem_biUnion.mp hE
  have hcard := card_le_card hCE
  rw [huniform i hi C hCi, huniform j hj E hEj] at hcard
  have hi4 := (mem_Icc.mp hi).1
  have hj4 := (mem_Icc.mp hj).1
  have hij : i ≤ j := by omega
  by_cases heq : i = j
  · apply eq_of_subset_of_card_le hCE
    rw [huniform i hi C hCi, huniform j hj E hEj, heq]
  · exact (havoid j hj E hEj C (mem_biUnion.mpr ⟨i, mem_Ico.mpr ⟨hi4, by omega⟩, hCi⟩) hCE).elim

theorem regularizedForbiddenUnion_minimal
    {V I : Type*} [DecidableEq V] [DecidableEq I]
    (e : I ↪ TripleOn V) (q : ℕ) (Lstar : ℕ → Finset (Finset I))
    (huniform : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, E.card = j - 2)
    (havoid : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, ∀ C ∈ (Ico 4 j).biUnion Lstar, ¬ C ⊆ E) :
    minimalForbiddenFamily (regularizedForbiddenUnion e q Lstar) = regularizedForbiddenUnion e q Lstar := by
  classical
  apply Subset.antisymm (minimalForbiddenFamily_subset _)
  intro E hE
  apply mem_filter.mpr
  refine ⟨hE, ?_⟩
  intro C hC hCE
  obtain ⟨E0, hE0, rfl⟩ := mem_image.mp hE
  obtain ⟨C0, hC0, rfl⟩ := mem_image.mp hC
  have heq := regularized_order_union_eq_of_subset q Lstar huniform havoid hC0 hE0 (map_subset_map.mp hCE)
  exact heq ▸ Subset.rfl

theorem regularizedForbiddenUnion_order
    {V I : Type*} [DecidableEq V] [DecidableEq I]
    (e : I ↪ TripleOn V) (q : ℕ) (Lstar : ℕ → Finset (Finset I))
    (huniform : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, E.card = j - 2) :
    ∀ E ∈ regularizedForbiddenUnion e q Lstar, 2 ≤ E.card ∧ E.card + 2 ≤ q := by
  intro E hE
  obtain ⟨E0, hE0, rfl⟩ := mem_image.mp hE
  obtain ⟨j, hj, hEj⟩ := mem_biUnion.mp hE0
  rw [card_map, huniform j hj E0 hEj]
  have hh := mem_Icc.mp hj
  constructor <;> omega

theorem SourceRegularizationOrderResult.decoded_packing
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I]
    {ell j b : ℕ} {W : Vortex V ell} {e : I ↪ TripleOn V}
    {L earlier Lstar : Finset (Finset I)} {F Fsup : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceRegularizationOrderResult W e j b L earlier F y z Lstar Fsup)
    (hL : ∀ E ∈ L, IsPackingOn (E.map e)) : ∀ E ∈ Lstar, IsPackingOn (E.map e) := by
  intro E hE
  by_cases hOld : E ∈ L
  · exact hL E hOld
  · exact (h.spread.uniform (E.map e) (h.contains_new_constraints
      (mem_image.mpr ⟨E, mem_sdiff.mpr ⟨hE, hOld⟩, rfl⟩))).2

theorem regularizedForbiddenUnion_packing
    {V I : Type*} [DecidableEq V] [DecidableEq I]
    (e : I ↪ TripleOn V) (q : ℕ) (Lstar : ℕ → Finset (Finset I))
    (hpacking : ∀ j ∈ Icc 4 q, ∀ E ∈ Lstar j, IsPackingOn (E.map e)) :
    ∀ E ∈ regularizedForbiddenUnion e q Lstar, IsPackingOn E := by
  intro E hE
  obtain ⟨E0, hE0, rfl⟩ := mem_image.mp hE
  obtain ⟨j, hj, hEj⟩ := mem_biUnion.mp hE0
  exact hpacking j hj E0 hEj

theorem avoids_original_union_of_regularized
    {V I : Type*} [DecidableEq V] [DecidableEq I]
    (e : I ↪ TripleOn V) (q : ℕ) (L Lstar : ℕ → Finset (Finset I))
    (hcovers : ∀ j ∈ Icc 4 q, ∀ E ∈ L j, ∃ C ∈ (Ico 4 j).biUnion Lstar ∪ Lstar j, C ⊆ E)
    (M : TripleSystemOn V) (havoid : AvoidsForbidden M (regularizedForbiddenUnion e q Lstar)) :
    AvoidsForbidden M (regularizedForbiddenUnion e q L) := by
  intro E hE hEM
  obtain ⟨E0, hE0, rfl⟩ := mem_image.mp hE
  obtain ⟨j, hj, hEj⟩ := mem_biUnion.mp hE0
  obtain ⟨C, hC, hCE⟩ := hcovers j hj E0 hEj
  have hCunion : C ∈ (Icc 4 q).biUnion Lstar := by
    rcases mem_union.mp hC with hold | hnew
    · obtain ⟨i, hi, hCi⟩ := mem_biUnion.mp hold
      have hib := mem_Ico.mp hi
      have hjb := mem_Icc.mp hj
      exact mem_biUnion.mpr ⟨i, mem_Icc.mpr ⟨hib.1, by omega⟩, hCi⟩
    · exact mem_biUnion.mpr ⟨j, hj, hnew⟩
  exact havoid (C.map e) (mem_image.mpr ⟨C, hCunion, rfl⟩) ((map_subset_map.mpr hCE).trans hEM)

end

end Erdos207
