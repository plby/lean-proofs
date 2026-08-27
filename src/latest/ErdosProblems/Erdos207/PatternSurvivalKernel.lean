/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternSurvival

/-! # The exact killed kernel for a surviving base pattern -/

namespace Erdos207

open Finset

noncomputable section

theorem greedyKernel_supported_patternCovered
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (S : GreedyStateOn V)
    (hQ : ¬ PatternUncovered Q S) :
    (greedyKernel F S).SupportedOn (fun S' ↦ ¬ PatternUncovered Q S') := by
  intro S' hmass
  rcases greedyKernel_supported_step_or_self F S S' hmass with rfl | ⟨T, _, rfl⟩
  · exact hQ
  · exact fun h ↦ hQ ((patternUncovered_greedyStep_iff F Q S T).mp h).1

theorem greedyKernel_expectationReal_patternUncovered
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (Q : SimpleGraph V)
    (hQ : PatternUncovered Q S) (hA : S.available.Nonempty)
    (φ : GreedyStateOn V → ℝ) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ if PatternUncovered Q S' then φ S' else 0) =
      (S.available.card : ℝ)⁻¹ *
        ∑ T ∈ patternSurvivalSelectors Q S, φ (greedyStep F S T) := by
  classical
  rw [greedyKernel_expectationReal_of_nonempty F S hA]
  congr 1
  calc
    (∑ T : S.available,
        if PatternUncovered Q (greedyStep F S T.1) then φ (greedyStep F S T.1) else 0) =
        ∑ T : S.available,
          if Disjoint (graphEdges Q) (tripleEdgeFinset T.1) then
            φ (greedyStep F S T.1) else 0 := by
      apply sum_congr rfl
      intro T _
      simp only [patternUncovered_greedyStep_iff, hQ, true_and]
    _ = ∑ T ∈ S.available,
        if Disjoint (graphEdges Q) (tripleEdgeFinset T) then
          φ (greedyStep F S T) else 0 := by
      rw [Finset.univ_eq_attach]
      exact sum_attach S.available
        (fun T ↦ if Disjoint (graphEdges Q) (tripleEdgeFinset T) then
          φ (greedyStep F S T) else 0)
    _ = _ := by rw [patternSurvivalSelectors, sum_filter]

theorem greedyKernel_expectationReal_patternUncovered_eq_restricted
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (Q : SimpleGraph V)
    (hQ : PatternUncovered Q S) (hA : S.available.Nonempty)
    (hR : (patternSurvivalSelectors Q S).Nonempty) (φ : GreedyStateOn V → ℝ) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ if PatternUncovered Q S' then φ S' else 0) =
      ((patternSurvivalSelectors Q S).card : ℝ) / S.available.card *
        (restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).expectationReal φ := by
  classical
  rw [greedyKernel_expectationReal_patternUncovered Q hQ hA,
    restrictedGreedyKernel_expectationReal]
  have hRpos : (0 : ℝ) < (patternSurvivalSelectors Q S).card := by
    exact_mod_cast card_pos.mpr hR
  field_simp

theorem greedyKernel_expectationReal_patternUncovered_le_of_restricted
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (Q : SimpleGraph V)
    (hQ : PatternUncovered Q S) (hA : S.available.Nonempty)
    (φ : GreedyStateOn V → ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hbound : ∀ hR : (patternSurvivalSelectors Q S).Nonempty,
      (restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).expectationReal φ ≤ v) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ if PatternUncovered Q S' then φ S' else 0) ≤ v := by
  classical
  by_cases hR : (patternSurvivalSelectors Q S).Nonempty
  · rw [greedyKernel_expectationReal_patternUncovered_eq_restricted Q hQ hA hR]
    have hApos : (0 : ℝ) < S.available.card := by exact_mod_cast card_pos.mpr hA
    have hratio : ((patternSurvivalSelectors Q S).card : ℝ) / S.available.card ≤ 1 := by
      apply (div_le_one hApos).mpr
      exact_mod_cast card_le_card (filter_subset
        (fun T ↦ Disjoint (graphEdges Q) (tripleEdgeFinset T)) S.available)
    calc
      _ ≤ (((patternSurvivalSelectors Q S).card : ℝ) / S.available.card) * v :=
        mul_le_mul_of_nonneg_left (hbound hR) (by positivity)
      _ ≤ 1 * v := mul_le_mul_of_nonneg_right hratio hv
      _ = v := one_mul v
  · rw [greedyKernel_expectationReal_patternUncovered Q hQ hA,
      not_nonempty_iff_eq_empty.mp hR, sum_empty, mul_zero]
    exact hv

end

end Erdos207
