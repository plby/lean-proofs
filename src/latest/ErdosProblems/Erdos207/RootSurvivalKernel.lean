/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyClosedThreatDrift
import ErdosProblems.Erdos207.GreedyConfigurationThreats

/-! # Root survival and the restricted uniform greedy kernel -/

namespace Erdos207

open Finset

noncomputable section

theorem root_mem_greedyStep_available_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {root T : TripleOn V}
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available) (hT : T ∈ S.available) :
    root ∈ (greedyStep F S T).available ↔ T ∉ greedyClosedThreats F S root := by
  rw [greedyStep_available_eq_sdiff_closedThreats hS hT, mem_sdiff,
    and_iff_right hroot, mem_greedyClosedThreats_comm F S hT hroot]

theorem greedyKernel_supported_rootDead
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (root : TripleOn V)
    (hdead : root ∉ S.available) :
    (greedyKernel F S).SupportedOn (fun S' ↦ root ∉ S'.available) := by
  intro S' hmass
  rcases greedyKernel_supported_step_or_self F S S' hmass with rfl | ⟨T, _, rfl⟩
  · exact hdead
  · intro h
    exact hdead (greedyStep_available_subset F S T h)

theorem greedyKernel_expectationReal_rootAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (root : TripleOn V)
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (φ : GreedyStateOn V → ℝ) :
    (greedyKernel F S).expectationReal
      (fun S' ↦ if root ∈ S'.available then φ S' else 0) =
      (S.available.card : ℝ)⁻¹ *
        ∑ T ∈ S.available \ greedyClosedThreats F S root, φ (greedyStep F S T) := by
  have hA : S.available.Nonempty := ⟨root, hroot⟩
  rw [greedyKernel_expectationReal_of_nonempty F S hA]
  congr 1
  calc
    (∑ T : S.available,
        if root ∈ (greedyStep F S T.1).available then φ (greedyStep F S T.1) else 0) =
        ∑ T : S.available,
          if T.1 ∉ greedyClosedThreats F S root then φ (greedyStep F S T.1) else 0 := by
      apply sum_congr rfl
      intro T _
      simp only [root_mem_greedyStep_available_iff hS hroot T.2]
    _ = ∑ T ∈ S.available,
        if T ∉ greedyClosedThreats F S root then φ (greedyStep F S T) else 0 := by
      rw [Finset.univ_eq_attach]
      simpa only using! sum_attach S.available
        (fun T ↦ if T ∉ greedyClosedThreats F S root then φ (greedyStep F S T) else 0)
    _ = _ := by
      rw [sdiff_eq_filter, sum_filter]

theorem greedyKernel_expectationReal_rootAlive_eq_restricted
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (root : TripleOn V)
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty)
    (φ : GreedyStateOn V → ℝ) :
    (greedyKernel F S).expectationReal
      (fun S' ↦ if root ∈ S'.available then φ S' else 0) =
      ((S.available \ greedyClosedThreats F S root).card : ℝ) / S.available.card *
        (restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal φ := by
  rw [greedyKernel_expectationReal_rootAlive root hS hroot,
    restrictedGreedyKernel_expectationReal]
  have hRpos : (0 : ℝ) < (S.available \ greedyClosedThreats F S root).card := by
    exact_mod_cast card_pos.mpr hR
  field_simp

/-- A nonnegative upper bound under the conditional law remains valid for
the survival-weighted observable under the original law. Empty survival
sets are handled without inventing a conditional probability. -/
theorem greedyKernel_expectationReal_rootAlive_le_of_restricted
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (root : TripleOn V)
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (φ : GreedyStateOn V → ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hbound : ∀ hR : (S.available \ greedyClosedThreats F S root).Nonempty,
      (restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal φ ≤ v) :
    (greedyKernel F S).expectationReal
      (fun S' ↦ if root ∈ S'.available then φ S' else 0) ≤ v := by
  by_cases hR : (S.available \ greedyClosedThreats F S root).Nonempty
  · rw [greedyKernel_expectationReal_rootAlive_eq_restricted root hS hroot hR]
    have hApos : (0 : ℝ) < S.available.card := by
      exact_mod_cast card_pos.mpr (show S.available.Nonempty from ⟨root, hroot⟩)
    have hratio : ((S.available \ greedyClosedThreats F S root).card : ℝ) /
        S.available.card ≤ 1 := by
      apply (div_le_one hApos).mpr
      exact_mod_cast card_le_card (sdiff_subset :
        S.available \ greedyClosedThreats F S root ⊆ S.available)
    calc
      _ ≤ (((S.available \ greedyClosedThreats F S root).card : ℝ) / S.available.card) * v :=
        mul_le_mul_of_nonneg_left (hbound hR) (by positivity)
      _ ≤ 1 * v := mul_le_mul_of_nonneg_right hratio hv
      _ = v := one_mul v
  · rw [greedyKernel_expectationReal_rootAlive root hS hroot,
      not_nonempty_iff_eq_empty.mp hR, sum_empty, mul_zero]
    exact hv

end

end Erdos207
