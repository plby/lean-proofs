/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.Prefix
import Mathlib.Data.Finset.Max

/-! # Removing redundant forbidden configurations without changing the process -/

namespace Erdos207

open Finset

noncomputable section

def minimalForbiddenFamily
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V) : ForbiddenFamilyOn V := by
  classical
  exact F.filter fun C ↦ ∀ D ∈ F, D ⊆ C → C ⊆ D

theorem minimalForbiddenFamily_subset
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V) :
    minimalForbiddenFamily F ⊆ F := filter_subset _ _

theorem exists_minimalForbiddenFamily_subset
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V}
    {C : TripleSystemOn V} (hC : C ∈ F) :
    ∃ D ∈ minimalForbiddenFamily F, D ⊆ C := by
  classical
  let candidates := F.filter fun D ↦ D ⊆ C
  have hne : candidates.Nonempty := ⟨C, mem_filter.mpr ⟨hC, Subset.rfl⟩⟩
  obtain ⟨D, hD, hmin⟩ := exists_min_image candidates Finset.card hne
  have hDF := (mem_filter.mp hD).1
  have hDC := (mem_filter.mp hD).2
  refine ⟨D, mem_filter.mpr ⟨hDF, ?_⟩, hDC⟩
  intro E hEF hED
  have hE : E ∈ candidates := mem_filter.mpr ⟨hEF, hED.trans hDC⟩
  have hcard := hmin E hE
  have heq : E = D := eq_of_subset_of_card_le hED hcard
  exact heq ▸ Subset.rfl

theorem eq_of_mem_minimalForbiddenFamily_of_subset
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V}
    {C D : TripleSystemOn V}
    (hC : C ∈ minimalForbiddenFamily F) (hD : D ∈ minimalForbiddenFamily F)
    (hCD : C ⊆ D) : C = D := by
  exact Subset.antisymm hCD ((mem_filter.mp hD).2 C
    (minimalForbiddenFamily_subset F hC) hCD)

theorem avoidsForbidden_minimal_iff
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V) (H : TripleSystemOn V) :
    AvoidsForbidden H (minimalForbiddenFamily F) ↔ AvoidsForbidden H F := by
  constructor
  · intro h C hCF hCH
    obtain ⟨D, hD, hDC⟩ := exists_minimalForbiddenFamily_subset hCF
    exact h D hD (hDC.trans hCH)
  · intro h C hCF
    exact h C (minimalForbiddenFamily_subset F hCF)

theorem isLegalExtension_minimal_iff
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (C : TripleSystemOn V) (T : TripleOn V) :
    IsLegalExtension (minimalForbiddenFamily F) C T ↔ IsLegalExtension F C T := by
  simp only [IsLegalExtension, avoidsForbidden_minimal_iff]

theorem legalAvailable_minimal_eq
    {V : Type*} [Fintype V] [DecidableEq V] (F : ForbiddenFamilyOn V)
    (C A : TripleSystemOn V) :
    legalAvailable (minimalForbiddenFamily F) C A = legalAvailable F C A := by
  ext T
  simp only [mem_legalAvailable_iff, isLegalExtension_minimal_iff]

theorem greedyStep_minimal_eq
    {V : Type*} [Fintype V] [DecidableEq V] (F : ForbiddenFamilyOn V)
    (S : GreedyStateOn V) (T : TripleOn V) :
    greedyStep (minimalForbiddenFamily F) S T = greedyStep F S T := by
  simp only [greedyStep, legalAvailable_minimal_eq]

theorem greedyKernel_minimal_eq
    {V : Type*} [Fintype V] [DecidableEq V] (F : ForbiddenFamilyOn V)
    (S : GreedyStateOn V) :
    greedyKernel (minimalForbiddenFamily F) S = greedyKernel F S := by
  classical
  unfold greedyKernel
  split_ifs <;> simp only [greedyStep_minimal_eq]

end

end Erdos207
