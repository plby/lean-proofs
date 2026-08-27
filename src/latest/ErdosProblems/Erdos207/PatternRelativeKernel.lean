/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternDriftError
import ErdosProblems.Erdos207.PatternExtensionMoments
import ErdosProblems.Erdos207.RelativeObservableArithmetic
import ErdosProblems.Erdos207.PatternSelectorArithmetic

/-! # Relative pattern statistics under the actual surviving-selector kernel -/

namespace Erdos207

open Finset

noncomputable section

def properPatternRelativeCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (U : Finset V) (f : ℝ) (S : GreedyStateOn V) : ℝ :=
  (properPatternExtensions S.available Q U).card / f

theorem restrictedGreedyKernel_pattern_relative_drift_error
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V)
    (hR : (patternSurvivalSelectors Q S).Nonempty)
    (f fp H A delta er tau : ℝ) (hf : 0 < f) (hfp : 0 < fp) (hA : 0 < A)
    (hbound : ∀ u ∈ properPatternExtensions S.available Q U,
      |((patternExtensionKillers F Q U S u).card : ℝ) - H| ≤ delta)
    (hdenom : |((patternSurvivalSelectors Q S).card : ℝ) - A| ≤ er)
    (hTaylor : |fp - f + f * H / A| ≤ tau) :
    |(restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).expectationReal (fun S' ↦
        properPatternRelativeCount Q U fp S' - properPatternRelativeCount Q U f S)| ≤
      ((properPatternExtensions S.available Q U).card / fp) *
        (delta / (patternSurvivalSelectors Q S).card +
          |H| * er / ((patternSurvivalSelectors Q S).card * A) + tau / f) := by
  let Y : ℝ := (properPatternExtensions S.available Q U).card
  let X := fun S' : GreedyStateOn V ↦ ((properPatternExtensions S'.available Q U).card : ℝ) - Y
  have hRpos : (0 : ℝ) < (patternSurvivalSelectors Q S).card := by exact_mod_cast card_pos.mpr hR
  have hraw := restrictedGreedyKernel_pattern_drift_error F Q U S hR H delta hbound
  have h := relative_observable_hazard_drift_error
    (restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR) X Y f fp H A
    (patternSurvivalSelectors Q S).card delta er tau (Nat.cast_nonneg _) hf hfp hA hRpos hraw hdenom hTaylor
  simpa only [X, Y, properPatternRelativeCount, add_sub_cancel] using h

theorem properPatternRelativeCount_step_jump
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V)
    (T : TripleOn V) (f fp J : ℝ) (hf : 0 < f) (hfp : 0 < fp)
    (hJ : ((patternExtensionLoss F Q U S T).card : ℝ) ≤ J) :
    |properPatternRelativeCount Q U fp (greedyStep F S T) - properPatternRelativeCount Q U f S| ≤
      (J + (properPatternExtensions S.available Q U).card * |fp - f| / f) / fp := by
  let Y : ℝ := (properPatternExtensions S.available Q U).card
  let X : ℝ := ((properPatternExtensions (greedyStep F S T).available Q U).card : ℝ) - Y
  have hX : |X| ≤ J := by
    dsimp only [X, Y]
    rw [properPatternExtensions_step_increment, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    exact hJ
  have h := relative_observable_jump_bound Y X f fp J (Nat.cast_nonneg _) hf hfp hX
  simpa only [X, Y, properPatternRelativeCount, add_sub_cancel] using h

theorem restrictedGreedyKernel_pattern_relative_secondMoment
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V)
    (hR : (patternSurvivalSelectors Q S).Nonempty)
    (f fp J H : ℝ) (hf : 0 < f) (hfp : 0 < fp) (hJ0 : 0 ≤ J)
    (hJ : ∀ T ∈ patternSurvivalSelectors Q S, ((patternExtensionLoss F Q U S T).card : ℝ) ≤ J)
    (hH : ∀ u ∈ properPatternExtensions S.available Q U,
      ((patternExtensionKillers F Q U S u).card : ℝ) ≤ H) :
    (restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).expectationReal (fun S' ↦
        (properPatternRelativeCount Q U fp S' - properPatternRelativeCount Q U f S) ^ 2) ≤
      (2 * (J * ((properPatternExtensions S.available Q U).card * H) / (patternSurvivalSelectors Q S).card) +
        2 * ((properPatternExtensions S.available Q U).card * (fp - f) / f) ^ 2) / fp ^ 2 := by
  let Y : ℝ := (properPatternExtensions S.available Q U).card
  let X := fun S' : GreedyStateOn V ↦ ((properPatternExtensions S'.available Q U).card : ℝ) - Y
  have hv := restrictedGreedyKernel_pattern_secondMoment_le_hazard F Q U S hR J H hJ0 hJ hH
  have h := relative_observable_secondMoment
    (restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR) X Y f fp _ hf.ne' hfp.ne' hv
  simpa only [X, Y, properPatternRelativeCount, add_sub_cancel] using h

end

end Erdos207
