/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.Prefix

/-!
# Configuration classes in the constrained greedy process

The class index counts already chosen triangles.  On a step this count
increases by exactly one precisely for configurations containing the
selector.  The other condition records that no member has been discarded.
-/

namespace Erdos207

open Finset

noncomputable section

def greedyConfigurationClass
    {V : Type*} [Fintype V] [DecidableEq V]
    (J : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (root : TripleOn V) (c : ℕ) : ForbiddenFamilyOn V :=
  J.filter fun C ↦ root ∈ C ∧ (C ∩ S.chosen).card = c ∧
    C ⊆ S.chosen ∪ S.available

@[simp] theorem mem_greedyConfigurationClass
    {V : Type*} [Fintype V] [DecidableEq V]
    {J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root : TripleOn V} {c : ℕ} {C : TripleSystemOn V} :
    C ∈ greedyConfigurationClass J S root c ↔
      C ∈ J ∧ root ∈ C ∧ (C ∩ S.chosen).card = c ∧
        C ⊆ S.chosen ∪ S.available := by
  simp [greedyConfigurationClass]

theorem card_inter_insert_of_not_mem
    {α : Type*} [DecidableEq α] (C A : Finset α) {x : α} (hx : x ∉ A) :
    (C ∩ insert x A).card = (C ∩ A).card + if x ∈ C then 1 else 0 := by
  by_cases hxC : x ∈ C
  · have hset : C ∩ insert x A = insert x (C ∩ A) := by
      ext y
      simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨hyC, h | h⟩
        · exact Or.inl h
        · exact Or.inr ⟨hyC, h⟩
      · rintro (rfl | h)
        · exact ⟨hxC, Or.inl rfl⟩
        · exact ⟨h.1, Or.inr h.2⟩
    rw [hset, card_insert_of_notMem (by simp [hx]), if_pos hxC]
  · have hset : C ∩ insert x A = C ∩ A := by
      ext y
      simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨hyC, h | h⟩
        · exact (hxC (h ▸ hyC)).elim
        · exact ⟨hyC, h⟩
      · exact fun h ↦ ⟨h.1, Or.inr h.2⟩
    simp [hset, hxC]

theorem greedyStep_chosen_union_available_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) {T : TripleOn V}
    (hT : T ∈ S.available) :
    (greedyStep F S T).chosen ∪ (greedyStep F S T).available ⊆
      S.chosen ∪ S.available := by
  intro U hU
  rcases mem_union.mp hU with hchosen | havailable
  · rcases mem_insert.mp hchosen with rfl | h
    · exact mem_union_right _ hT
    · exact mem_union_left _ h
  · exact mem_union_right _
      (mem_of_mem_erase (mem_legalAvailable_iff.mp havailable).1)

theorem greedyConfigurationClass_step_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {T root : TripleOn V} {c : ℕ} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    C ∈ greedyConfigurationClass J (greedyStep F S T) root c ↔
      C ∈ J ∧ root ∈ C ∧
        (C ∩ S.chosen).card + (if T ∈ C then 1 else 0) = c ∧
          C ⊆ (greedyStep F S T).chosen ∪ (greedyStep F S T).available := by
  rw [mem_greedyConfigurationClass]
  have hnew : T ∉ S.chosen := (hS.2.2 T hT).1
  change (_ ∧ _ ∧ (C ∩ insert T S.chosen).card = c ∧ _) ↔ _
  rw [card_inter_insert_of_not_mem C S.chosen hnew]

/-- A configuration in the next class either stayed in its old class or
arrived from exactly the preceding class by selecting one of its members. -/
theorem greedyConfigurationClass_step_succ_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {T root : TripleOn V} {c : ℕ} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    C ∈ greedyConfigurationClass J (greedyStep F S T) root (c + 1) ↔
      ((C ∈ greedyConfigurationClass J S root (c + 1) ∧ T ∉ C) ∨
        (C ∈ greedyConfigurationClass J S root c ∧ T ∈ C)) ∧
          C ⊆ (greedyStep F S T).chosen ∪ (greedyStep F S T).available := by
  rw [greedyConfigurationClass_step_iff hS hT]
  have hcover := greedyStep_chosen_union_available_subset F S hT
  constructor
  · rintro ⟨hCJ, hroot, hcount, hnext⟩
    refine ⟨?_, hnext⟩
    by_cases hTC : T ∈ C
    · right
      refine ⟨mem_greedyConfigurationClass.mpr ⟨hCJ, hroot, ?_, hnext.trans hcover⟩, hTC⟩
      simpa [hTC] using hcount
    · left
      refine ⟨mem_greedyConfigurationClass.mpr ⟨hCJ, hroot, ?_, hnext.trans hcover⟩, hTC⟩
      simpa [hTC] using hcount
  · rintro ⟨h | h, hnext⟩
    · obtain ⟨hCJ, hroot, hcount, _⟩ := mem_greedyConfigurationClass.mp h.1
      exact ⟨hCJ, hroot, by simpa [h.2] using hcount, hnext⟩
    · obtain ⟨hCJ, hroot, hcount, _⟩ := mem_greedyConfigurationClass.mp h.1
      exact ⟨hCJ, hroot, by simp [h.2, hcount], hnext⟩

theorem greedyConfigurationClass_step_zero_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {T root : TripleOn V} {C : TripleSystemOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    C ∈ greedyConfigurationClass J (greedyStep F S T) root 0 ↔
      C ∈ greedyConfigurationClass J S root 0 ∧ T ∉ C ∧
        C ⊆ (greedyStep F S T).chosen ∪ (greedyStep F S T).available := by
  rw [greedyConfigurationClass_step_iff hS hT]
  have hcover := greedyStep_chosen_union_available_subset F S hT
  constructor
  · rintro ⟨hCJ, hroot, hcount, hnext⟩
    have hTC : T ∉ C := by
      intro h
      simp [h] at hcount
    refine ⟨mem_greedyConfigurationClass.mpr ⟨hCJ, hroot, ?_, hnext.trans hcover⟩,
      hTC, hnext⟩
    simpa [hTC] using hcount
  · rintro ⟨hC, hTC, hnext⟩
    obtain ⟨hCJ, hroot, hcount, _⟩ := mem_greedyConfigurationClass.mp hC
    exact ⟨hCJ, hroot, by simpa [hTC] using hcount, hnext⟩

end

end Erdos207
