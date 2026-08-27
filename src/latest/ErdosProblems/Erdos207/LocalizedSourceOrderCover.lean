/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalForbiddenConfiguration
import ErdosProblems.Erdos207.TerminalConfigurationCount

/-! # Extracting fixed-source covers and restricting them to admissible source orders -/

namespace Erdos207

open Finset

noncomputable section

theorem localized_union_source_cover
    {V I : Type*} [DecidableEq V] [DecidableEq I]
    (indices : Finset I) (F : I → ForbiddenFamilyOn V) (orders : Finset ℕ)
    (J : ForbiddenFamilyOn V) (available old : TripleSystemOn V)
    (hJ : J ⊆ orders.biUnion (fun j ↦ localForbiddenConfigurations (indices.biUnion F) available old j)) :
    ∀ C ∈ J, C ⊆ available ∧ ∃ i : indices, ∃ E ∈ F i.1, C ⊆ E ∧ E \ C ⊆ old := by
  intro C hC
  obtain ⟨j, _hj, hlocal⟩ := mem_biUnion.mp (hJ hC)
  obtain ⟨hCA, _hcard, E, hE, hCE, hOld⟩ :=
    (mem_localForbiddenConfigurations_iff (indices.biUnion F) available old C j).mp hlocal
  obtain ⟨i, hi, hEi⟩ := mem_biUnion.mp hE
  exact ⟨hCA, ⟨i, hi⟩, E, hEi, hCE, hOld⟩

theorem source_cover_restrict_order
    {V I : Type*} [DecidableEq V] (F : I → ForbiddenFamilyOn V) (order : I → ℕ)
    (J : ForbiddenFamilyOn V) (available old : TripleSystemOn V) (j : ℕ) (hj : 4 ≤ j)
    (huniform : ∀ i E, E ∈ F i → E.card = order i - 2)
    (hJ : ∀ C ∈ J, C ⊆ available ∧ ∃ i E, E ∈ F i ∧ C ⊆ E ∧ E \ C ⊆ old) :
    ∀ C ∈ forbiddenFamilyOfOrder J j, C.card = j - 2 ∧ C ⊆ available ∧
      ∃ i : {i : I // j ≤ order i}, ∃ E ∈ F i.1, C ⊆ E ∧ E \ C ⊆ old := by
  intro C hC
  have hd := mem_forbiddenFamilyOfOrder.mp hC
  obtain ⟨hCA, i, E, hE, hCE, hOld⟩ := hJ C hd.1
  have hcard := card_le_card hCE
  rw [hd.2, huniform i E hE] at hcard
  exact ⟨hd.2, hCA, ⟨i, by omega⟩, E, hE, hCE, hOld⟩

end

end Erdos207
