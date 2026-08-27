/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.Core
import ErdosProblems.Erdos207.MinimalForbiddenFamily

/-! # Discarding non-packing obstructions does not change the greedy process -/

namespace Erdos207

open Finset

noncomputable section

def packingForbiddenFamily
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V) : ForbiddenFamilyOn V := by
  classical
  exact F.filter IsPackingOn

theorem packingForbiddenFamily_subset
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V) :
    packingForbiddenFamily F ⊆ F := by
  classical
  exact filter_subset _ _

theorem isPacking_of_mem_packingForbiddenFamily
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V} {C : TripleSystemOn V}
    (hC : C ∈ packingForbiddenFamily F) : IsPackingOn C := by
  classical
  exact (mem_filter.mp hC).2

theorem avoidsForbidden_packing_iff
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    {H : TripleSystemOn V} (hH : IsPackingOn H) :
    AvoidsForbidden H (packingForbiddenFamily F) ↔ AvoidsForbidden H F := by
  classical
  constructor
  · intro h C hCF hCH
    exact h C (mem_filter.mpr ⟨hCF, hH.mono hCH⟩) hCH
  · intro h C hCF
    exact h C (packingForbiddenFamily_subset F hCF)

theorem isLegalExtension_packing_iff
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (C : TripleSystemOn V) (T : TripleOn V) :
    IsLegalExtension (packingForbiddenFamily F) C T ↔ IsLegalExtension F C T := by
  constructor
  · rintro ⟨hnew, hpack, havoid⟩
    exact ⟨hnew, hpack, (avoidsForbidden_packing_iff F hpack).mp havoid⟩
  · rintro ⟨hnew, hpack, havoid⟩
    exact ⟨hnew, hpack, (avoidsForbidden_packing_iff F hpack).mpr havoid⟩

theorem legalAvailable_packing_eq
    {V : Type*} [Fintype V] [DecidableEq V] (F : ForbiddenFamilyOn V)
    (C A : TripleSystemOn V) :
    legalAvailable (packingForbiddenFamily F) C A = legalAvailable F C A := by
  ext T
  simp only [mem_legalAvailable_iff, isLegalExtension_packing_iff]

theorem greedyStep_packing_eq
    {V : Type*} [Fintype V] [DecidableEq V] (F : ForbiddenFamilyOn V)
    (S : GreedyStateOn V) (T : TripleOn V) :
    greedyStep (packingForbiddenFamily F) S T = greedyStep F S T := by
  simp only [greedyStep, legalAvailable_packing_eq]

theorem greedyKernel_packing_eq
    {V : Type*} [Fintype V] [DecidableEq V] (F : ForbiddenFamilyOn V)
    (S : GreedyStateOn V) :
    greedyKernel (packingForbiddenFamily F) S = greedyKernel F S := by
  classical
  unfold greedyKernel
  split_ifs <;> simp only [greedyStep_packing_eq]

theorem greedyKernel_minimal_packing_eq
    {V : Type*} [Fintype V] [DecidableEq V] (F : ForbiddenFamilyOn V)
    (S : GreedyStateOn V) :
    greedyKernel (minimalForbiddenFamily (packingForbiddenFamily F)) S =
      greedyKernel F S := by
  rw [greedyKernel_minimal_eq, greedyKernel_packing_eq]

end

end Erdos207
