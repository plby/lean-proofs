/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MinimalForbiddenFamily
import ErdosProblems.Erdos207.AbsorberGreedy

/-! # Restricting the initial forbidden family to available triangles -/

namespace Erdos207

open Finset

noncomputable section

def restrictForbiddenFamily
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V) (ambient : TripleSystemOn V) : ForbiddenFamilyOn V :=
  F.filter fun C ↦ C ⊆ ambient

theorem avoidsForbidden_restrict_iff
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V) (ambient H : TripleSystemOn V)
    (hH : H ⊆ ambient) : AvoidsForbidden H (restrictForbiddenFamily F ambient) ↔ AvoidsForbidden H F := by
  constructor
  · intro h C hC hCH
    exact h C (mem_filter.mpr ⟨hC, hCH.trans hH⟩) hCH
  · intro h C hC
    exact h C (mem_filter.mp hC).1

theorem avoidsForbidden_minimal_restrict_iff
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V) (ambient H : TripleSystemOn V)
    (hH : H ⊆ ambient) :
    AvoidsForbidden H (minimalForbiddenFamily (restrictForbiddenFamily F ambient)) ↔ AvoidsForbidden H F := by
  rw [avoidsForbidden_minimal_iff, avoidsForbidden_restrict_iff F ambient H hH]

theorem isLegalExtension_restrict_iff
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V) (ambient C : TripleSystemOn V)
    (T : TripleOn V) (hC : C ⊆ ambient) (hT : T ∈ ambient) :
    IsLegalExtension (restrictForbiddenFamily F ambient) C T ↔ IsLegalExtension F C T := by
  unfold IsLegalExtension
  rw [avoidsForbidden_restrict_iff F ambient (insert T C) (insert_subset_iff.mpr ⟨hT, hC⟩)]

theorem mem_minimal_restrict_subset
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V} {ambient C : TripleSystemOn V}
    (hC : C ∈ minimalForbiddenFamily (restrictForbiddenFamily F ambient)) : C ∈ F ∧ C ⊆ ambient :=
  mem_filter.mp (minimalForbiddenFamily_subset _ hC)

theorem restrictForbiddenFamily_card_ge_two
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V} {ambient C : TripleSystemOn V}
    (hnonempty : ∀ D ∈ F, D.Nonempty)
    (hlegal : ∀ T ∈ ambient, IsLegalExtension F ∅ T)
    (hC : C ∈ restrictForbiddenFamily F ambient) : 2 ≤ C.card := by
  obtain ⟨hCF, hCA⟩ := mem_filter.mp hC
  have hcpos : 0 < C.card := card_pos.mpr (hnonempty C hCF)
  by_contra hsmall
  have hone : C.card = 1 := by omega
  obtain ⟨T, rfl⟩ := card_eq_one.mp hone
  have hT : T ∈ ambient := hCA (mem_singleton_self T)
  exact (hlegal T hT).2.2 {T} hCF (by simp)

theorem exists_proper_subset_of_not_mem_minimal_restrict
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V} {ambient C : TripleSystemOn V}
    (hCF : C ∈ F) (hCA : C ⊆ ambient)
    (hnot : C ∉ minimalForbiddenFamily (restrictForbiddenFamily F ambient)) :
    ∃ D ∈ restrictForbiddenFamily F ambient, D ⊆ C ∧ ¬ C ⊆ D := by
  classical
  by_contra hnone
  apply hnot
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨hCF, hCA⟩, ?_⟩
  intro D hD hDC
  by_contra hCD
  exact hnone ⟨D, hD, hDC, hCD⟩

end

end Erdos207
