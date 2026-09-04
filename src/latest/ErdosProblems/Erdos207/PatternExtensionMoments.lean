/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternLocalizedJump

/-! # Conditional increment and second-moment bounds on the surviving-choice law -/

namespace Erdos207

open Finset

noncomputable section

theorem restrictedGreedyKernel_supported_step
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (R : TripleSystemOn V) (hR : R.Nonempty) :
    (restrictedGreedyKernel F S R hR).SupportedOn
      (fun S' ↦ ∃ T ∈ R, S' = greedyStep F S T) := by
  classical
  let : Nonempty R := ⟨⟨hR.choose, hR.choose_spec⟩⟩
  exact (FiniteLaw.uniform_supported (fun _ : R ↦ True) (fun _ ↦ trivial)).map
    (fun T : R ↦ greedyStep F S T.1) (fun T _ ↦ ⟨T.1, T.2, rfl⟩)

theorem restrictedGreedyKernel_pattern_increment_interval
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V)
    (hR : (patternSurvivalSelectors Q S).Nonempty) (J : ℝ)
    (hJ : ∀ T ∈ patternSurvivalSelectors Q S, ((patternExtensionLoss F Q U S T).card : ℝ) ≤ J) :
    (restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).SupportedOn (fun S' ↦
      -J ≤ ((properPatternExtensions S'.available Q U).card : ℝ) -
          (properPatternExtensions S.available Q U).card ∧
      ((properPatternExtensions S'.available Q U).card : ℝ) -
          (properPatternExtensions S.available Q U).card ≤ 0) := by
  intro S' hmass
  obtain ⟨T, hT, rfl⟩ := restrictedGreedyKernel_supported_step F S _ hR S' hmass
  rw [properPatternExtensions_step_increment]
  exact ⟨neg_le_neg (hJ T hT), neg_nonpos.mpr (Nat.cast_nonneg _)⟩

theorem restrictedGreedyKernel_pattern_secondMoment
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V)
    (hR : (patternSurvivalSelectors Q S).Nonempty) (J : ℝ)
    (hJ : ∀ T ∈ patternSurvivalSelectors Q S, ((patternExtensionLoss F Q U S T).card : ℝ) ≤ J) :
    (restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).expectationReal (fun S' ↦
      (((properPatternExtensions S'.available Q U).card : ℝ) -
        (properPatternExtensions S.available Q U).card) ^ 2) ≤
      J * (∑ u ∈ properPatternExtensions S.available Q U,
        ((patternExtensionKillers F Q U S u).card : ℝ)) / (patternSurvivalSelectors Q S).card := by
  let L := restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR
  let X := fun S' : GreedyStateOn V ↦ ((properPatternExtensions S'.available Q U).card : ℝ) -
    (properPatternExtensions S.available Q U).card
  have hpoint := restrictedGreedyKernel_pattern_increment_interval F Q U S hR J hJ
  calc
    _ ≤ L.expectationReal (fun S' ↦ -J * X S') := by
      apply L.expectationReal_mono_of_supported hpoint
      intro S' hS'
      change -J ≤ X S' ∧ X S' ≤ 0 at hS'
      have hprod := mul_nonneg (show 0 ≤ X S' + J by linarith only [hS'.1])
        (show 0 ≤ -X S' by linarith only [hS'.2])
      change X S' ^ 2 ≤ -J * X S'
      nlinarith only [hprod]
    _ = -J * L.expectationReal X := FiniteLaw.expectationReal_const_mul _ _ _
    _ = _ := by
      dsimp only [L, X]
      rw [restrictedGreedyKernel_properPatternExtension_drift]
      ring

theorem restrictedGreedyKernel_pattern_secondMoment_le_hazard
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V)
    (hR : (patternSurvivalSelectors Q S).Nonempty) (J H : ℝ) (hJ0 : 0 ≤ J)
    (hJ : ∀ T ∈ patternSurvivalSelectors Q S, ((patternExtensionLoss F Q U S T).card : ℝ) ≤ J)
    (hH : ∀ u ∈ properPatternExtensions S.available Q U, ((patternExtensionKillers F Q U S u).card : ℝ) ≤ H) :
    (restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).expectationReal (fun S' ↦
      (((properPatternExtensions S'.available Q U).card : ℝ) -
        (properPatternExtensions S.available Q U).card) ^ 2) ≤
      J * ((properPatternExtensions S.available Q U).card * H) / (patternSurvivalSelectors Q S).card := by
  apply (restrictedGreedyKernel_pattern_secondMoment F Q U S hR J hJ).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hJ0
  calc
    _ ≤ ∑ _u ∈ properPatternExtensions S.available Q U, H := sum_le_sum hH
    _ = _ := by simp

end

end Erdos207
