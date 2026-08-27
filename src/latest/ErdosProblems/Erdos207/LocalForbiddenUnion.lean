/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalForbiddenConfiguration
import ErdosProblems.Erdos207.ForbiddenFamilyDegreeUnion

/-! # Local forbidden families commute with finite unions of source orders -/

namespace Erdos207

open Finset

noncomputable section

theorem localForbiddenConfigurations_biUnion
    {V I : Type*} [DecidableEq V] [DecidableEq I]
    (indices : Finset I) (F : I → ForbiddenFamilyOn V)
    (available old : TripleSystemOn V) (j : ℕ) :
    localForbiddenConfigurations (indices.biUnion F) available old j =
      indices.biUnion (fun i ↦ localForbiddenConfigurations (F i) available old j) := by
  classical
  ext S
  simp only [mem_localForbiddenConfigurations_iff, mem_biUnion]
  constructor
  · rintro ⟨hSA, hSc, E, ⟨i, hi, hE⟩, hSE, hold⟩
    exact ⟨i, hi, hSA, hSc, E, hE, hSE, hold⟩
  · rintro ⟨i, hi, hSA, hSc, E, hE, hSE, hold⟩
    exact ⟨hSA, hSc, E, ⟨i, hi, hE⟩, hSE, hold⟩

theorem localForbiddenConfigurations_empty_of_smaller_order
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (available old : TripleSystemOn V) (j j' : ℕ)
    (hj : 3 ≤ j) (hjj : j' < j) (hF : ∀ E ∈ F, E.card = j' - 2) :
    localForbiddenConfigurations F available old j = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨_, hSc, E, hE, hSE, _⟩ :=
    (mem_localForbiddenConfigurations_iff F available old S j).mp hS
  have hEc := hF E hE
  have hc := card_le_card hSE
  omega

theorem localForbiddenConfigurations_order_union
    {V : Type*} [DecidableEq V] (F : ℕ → ForbiddenFamilyOn V)
    (available old : TripleSystemOn V) (j q : ℕ) (hj : 4 ≤ j)
    (hF : ∀ j' ∈ Icc 4 q, ∀ E ∈ F j', E.card = j' - 2) :
    localForbiddenConfigurations ((Icc 4 q).biUnion F) available old j =
      (Icc j q).biUnion (fun j' ↦ localForbiddenConfigurations (F j') available old j) := by
  classical
  rw [localForbiddenConfigurations_biUnion]
  ext S
  simp only [mem_biUnion, mem_Icc]
  constructor
  · rintro ⟨j', ⟨hj'4, hj'q⟩, hS⟩
    have hjj' : j ≤ j' := by
      by_contra hn
      have hempty := localForbiddenConfigurations_empty_of_smaller_order (F j')
        available old j j' (by omega) (by omega) (hF j' (mem_Icc.mpr ⟨hj'4, hj'q⟩))
      simpa [hempty] using hS
    exact ⟨j', ⟨hjj', hj'q⟩, hS⟩
  · rintro ⟨j', ⟨hjj', hj'q⟩, hS⟩
    exact ⟨j', ⟨hj.trans hjj', hj'q⟩, hS⟩

end

end Erdos207
