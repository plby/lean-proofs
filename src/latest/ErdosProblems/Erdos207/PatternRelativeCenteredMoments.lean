/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternRelativeCentered

/-! # Actual centered relative-pattern jump and second moment -/

namespace Erdos207

open Finset

noncomputable section

theorem restrictedGreedyKernel_pattern_relative_centered_moments
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V)
    (hR : (patternSurvivalSelectors Q S).Nonempty)
    (target envelope : ℝ → ℝ) (sigma time L x J G D Z : ℝ)
    (hsigma : |sigma| = 1) (hf : 0 < target time)
    (hnext : target time / 2 ≤ target (time + 1))
    (hY : ((properPatternExtensions S.available Q U).card : ℝ) ≤ 2 * target time)
    (hfL : target time ≤ L) (hx : 0 < x) (hJ : 1 ≤ J) (hG : 0 ≤ G) (hD : 0 ≤ D) (hZ : 0 ≤ Z)
    (hRlower : L * x / 6 ≤ ((patternSurvivalSelectors Q S).card : ℝ))
    (hLoss : ∀ T ∈ patternSurvivalSelectors Q S, ((patternExtensionLoss F Q U S T).card : ℝ) ≤ J)
    (hHazard : ∀ u ∈ properPatternExtensions S.available Q U, ((patternExtensionKillers F Q U S u).card : ℝ) ≤ G * x)
    (hstep : |target (time + 1) - target time| / target time ≤ D / L)
    (henv : |envelope (time + 1) - envelope time| ≤ Z / L) :
    (∀ T ∈ patternSurvivalSelectors Q S,
      |patternRelativeCenteredObservable Q U target envelope sigma (time + 1) (greedyStep F S T) -
        patternRelativeCenteredObservable Q U target envelope sigma time S| ≤
          (2 + 4 * D + Z) * J / target time) ∧
    (restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).expectationReal (fun S' ↦
      (patternRelativeCenteredObservable Q U target envelope sigma (time + 1) S' -
        patternRelativeCenteredObservable Q U target envelope sigma time S) ^ 2) ≤
          (192 * G + 64 * D ^ 2 + 2 * Z ^ 2) * J / (target time * L) := by
  let Y : ℝ := (properPatternExtensions S.available Q U).card
  let law := restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR
  let X := fun S' ↦ properPatternRelativeCount Q U (target (time + 1)) S' -
    properPatternRelativeCount Q U (target time) S
  have hfp : 0 < target (time + 1) := (by positivity : 0 < target time / 2).trans_le hnext
  have hL : 0 < L := hf.trans_le hfL
  have hJ0 : 0 ≤ J := by linarith
  have hY0 : 0 ≤ Y := Nat.cast_nonneg _
  have hrawVariance : J * (Y * (G * x)) / (patternSurvivalSelectors Q S).card ≤ 6 * G * J * Y / L := by
    calc
      _ ≤ J * (Y * (G * x)) / (L * x / 6) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hRlower
      _ = _ := by field_simp
  have hrelVariance := restrictedGreedyKernel_pattern_relative_secondMoment F Q U S hR
    (target time) (target (time + 1)) J (G * x) hf hfp hJ0 hLoss hHazard
  have hrelBudget := relative_pattern_clock_secondMoment_budget Y (target time) (target (time + 1)) L J D G
    (J * (Y * (G * x)) / (patternSurvivalSelectors Q S).card) hY0 hf hY hnext hfL hJ hD hG hstep hrawVariance
  have hrelative : law.expectationReal (fun S' ↦ X S' ^ 2) ≤
      (96 * G + 32 * D ^ 2) * J / (target time * L) := hrelVariance.trans hrelBudget
  constructor
  · intro T hT
    have hrawJump := properPatternRelativeCount_step_jump F Q U S T (target time) (target (time + 1)) J
      hf hfp (hLoss T hT)
    have hbudget := relative_pattern_clock_jump_budget Y (target time) (target (time + 1)) L J D
      hY0 hf hY hnext hfL hJ hD hstep
    rw [patternRelativeCenteredObservable_increment]
    exact relative_pattern_centered_clock_jump_budget _ sigma (envelope (time + 1) - envelope time)
      (target time) L J D Z hf hfL hJ hZ hsigma (hrawJump.trans hbudget) henv
  · have hcenter := relative_pattern_centered_clock_secondMoment_budget law X sigma
      (envelope (time + 1) - envelope time) (target time) L J D G Z hf hfL hJ hsigma hrelative henv
    simpa only [patternRelativeCenteredObservable_increment] using hcenter

end

end Erdos207
