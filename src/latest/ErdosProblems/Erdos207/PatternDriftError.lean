/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternHazardTrajectory
import ErdosProblems.Erdos207.DriftErrorArithmetic

/-! # From the extension hazard estimate to the normalized actual drift -/

namespace Erdos207

open Finset

noncomputable section

theorem restrictedGreedyKernel_pattern_drift_error
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V)
    (hR : (patternSurvivalSelectors Q S).Nonempty)
    (H delta : ℝ)
    (hbound : ∀ u ∈ properPatternExtensions S.available Q U,
      |((patternExtensionKillers F Q U S u).card : ℝ) - H| ≤ delta) :
    |(restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).expectationReal (fun S' ↦
        ((properPatternExtensions S'.available Q U).card : ℝ) -
          (properPatternExtensions S.available Q U).card) +
        (properPatternExtensions S.available Q U).card * H / (patternSurvivalSelectors Q S).card| ≤
      (properPatternExtensions S.available Q U).card * delta / (patternSurvivalSelectors Q S).card := by
  have hRpos : (0 : ℝ) < (patternSurvivalSelectors Q S).card := by
    exact_mod_cast card_pos.mpr hR
  have hsum := abs_sum_sub_card_mul_le_sum_error (properPatternExtensions S.available Q U)
    (fun u ↦ ((patternExtensionKillers F Q U S u).card : ℝ)) (fun _ ↦ delta) H hbound
  simp only [sum_const, nsmul_eq_mul] at hsum
  rw [restrictedGreedyKernel_properPatternExtension_drift]
  have heq : -(∑ u ∈ properPatternExtensions S.available Q U,
      ((patternExtensionKillers F Q U S u).card : ℝ)) / (patternSurvivalSelectors Q S).card +
      (properPatternExtensions S.available Q U).card * H / (patternSurvivalSelectors Q S).card =
      -((∑ u ∈ properPatternExtensions S.available Q U,
        ((patternExtensionKillers F Q U S u).card : ℝ)) -
          (properPatternExtensions S.available Q U).card * H) / (patternSurvivalSelectors Q S).card := by ring
  rw [heq, abs_div, abs_neg, abs_of_pos hRpos]
  exact div_le_div_of_nonneg_right hsum hRpos.le

theorem restrictedGreedyKernel_pattern_target_drift_error
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V)
    (hR : (patternSurvivalSelectors Q S).Nonempty)
    (H delta f z A er : ℝ) (hA : 0 < A)
    (hbound : ∀ u ∈ properPatternExtensions S.available Q U,
      |((patternExtensionKillers F Q U S u).card : ℝ) - H| ≤ delta)
    (hband : |((properPatternExtensions S.available Q U).card : ℝ) - f| ≤ z)
    (hdenom : |((patternSurvivalSelectors Q S).card : ℝ) - A| ≤ er) :
    |(restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).expectationReal (fun S' ↦
        ((properPatternExtensions S'.available Q U).card : ℝ) -
          (properPatternExtensions S.available Q U).card) + f * H / A| ≤
      ((properPatternExtensions S.available Q U).card * delta + z * |H|) /
          (patternSurvivalSelectors Q S).card +
        |f * H| * er / ((patternSurvivalSelectors Q S).card * A) := by
  let total := ∑ u ∈ properPatternExtensions S.available Q U,
    ((patternExtensionKillers F Q U S u).card : ℝ)
  let Y : ℝ := (properPatternExtensions S.available Q U).card
  have hsum := abs_sum_sub_card_mul_le_sum_error (properPatternExtensions S.available Q U)
    (fun u ↦ ((patternExtensionKillers F Q U S u).card : ℝ)) (fun _ ↦ delta) H hbound
  simp only [sum_const, nsmul_eq_mul] at hsum
  have hnum : |total - f * H| ≤ Y * delta + z * |H| := by
    calc
      _ ≤ |total - Y * H| + |Y * H - f * H| := abs_sub_le _ _ _
      _ = |total - Y * H| + |Y - f| * |H| := by rw [← sub_mul, abs_mul]
      _ ≤ _ := add_le_add hsum (mul_le_mul_of_nonneg_right hband (abs_nonneg H))
  have hRpos : (0 : ℝ) < (patternSurvivalSelectors Q S).card := by exact_mod_cast card_pos.mpr hR
  have h := abs_div_sub_div_le_of_errors hRpos hA hnum hdenom
  rw [restrictedGreedyKernel_properPatternExtension_drift]
  have heq : -total / (patternSurvivalSelectors Q S).card + f * H / A =
      -(total / (patternSurvivalSelectors Q S).card - f * H / A) := by ring
  change |-total / (patternSurvivalSelectors Q S).card + f * H / A| ≤ _
  rw [heq, abs_neg]
  exact h

end

end Erdos207
