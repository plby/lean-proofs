/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternRelativeKernel
import ErdosProblems.Erdos207.RelativePatternClockMoments

/-! # Centered relative-pattern observables and their actual kernel drift -/

namespace Erdos207

open Finset

noncomputable section

def patternRelativeCenteredObservable
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (U : Finset V) (target envelope : ℝ → ℝ)
    (sigma time : ℝ) (S : GreedyStateOn V) : ℝ :=
  sigma * (properPatternRelativeCount Q U (target time) S - 1) - envelope time

theorem patternRelativeCenteredObservable_increment
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (U : Finset V) (target envelope : ℝ → ℝ)
    (sigma time : ℝ) (S S' : GreedyStateOn V) :
    patternRelativeCenteredObservable Q U target envelope sigma (time + 1) S' -
      patternRelativeCenteredObservable Q U target envelope sigma time S =
      sigma * (properPatternRelativeCount Q U (target (time + 1)) S' -
        properPatternRelativeCount Q U (target time) S) - (envelope (time + 1) - envelope time) := by
  unfold patternRelativeCenteredObservable
  ring

theorem restrictedGreedyKernel_pattern_relative_centered_drift
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V)
    (hR : (patternSurvivalSelectors Q S).Nonempty)
    (target envelope : ℝ → ℝ) (sigma time C G e L x H A tau : ℝ)
    (hsigma : |sigma| = 1) (hf : 0 < target time)
    (hnext : target time / 2 ≤ target (time + 1))
    (hY : ((properPatternExtensions S.available Q U).card : ℝ) ≤ 2 * target time)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (he : 0 ≤ e) (hL : 0 < L) (hx : 0 < x)
    (hdenLower : L * x / 6 ≤ ((patternSurvivalSelectors Q S).card : ℝ))
    (hA : A = L * x / 3) (hH : |H| ≤ G * x)
    (hdenom : |((patternSurvivalSelectors Q S).card : ℝ) - A| ≤ 2 * L * e / 3)
    (hbound : ∀ u ∈ properPatternExtensions S.available Q U,
      |((patternExtensionKillers F Q U S u).card : ℝ) - H| ≤ C * e)
    (hTaylor : |target (time + 1) - target time + target time * H / A| ≤ tau)
    (hcover : 8 * (C + 2 * G) * e / x ≤ envelope time)
    (hTaylorSmall : 4 * tau / target time ≤ 3 * envelope time / L)
    (hgrowth : 6 * envelope time / L ≤ envelope (time + 1) - envelope time) :
    (restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR).expectationReal (fun S' ↦
      patternRelativeCenteredObservable Q U target envelope sigma (time + 1) S' -
        patternRelativeCenteredObservable Q U target envelope sigma time S) ≤ 0 := by
  let law := restrictedGreedyKernel F S (patternSurvivalSelectors Q S) hR
  let X := fun S' ↦ properPatternRelativeCount Q U (target (time + 1)) S' -
    properPatternRelativeCount Q U (target time) S
  have hfp : 0 < target (time + 1) := (by positivity : 0 < target time / 2).trans_le hnext
  have hApos : 0 < A := by rw [hA]; positivity
  have htau : 0 ≤ tau := (abs_nonneg _).trans hTaylor
  have hraw := restrictedGreedyKernel_pattern_relative_drift_error F Q U S hR
    (target time) (target (time + 1)) H A (C * e) (2 * L * e / 3) tau
    hf hfp hApos hbound hdenom hTaylor
  have hrate := pattern_relative_hazard_rate_le C G e L x H (patternSurvivalSelectors Q S).card A
    (2 * L * e / 3) hC hG he hL hx hdenLower hA hH le_rfl
  have hprefactor := (relative_pattern_prefactor_bounds
    (properPatternExtensions S.available Q U).card (target time) (target (time + 1))
    (Nat.cast_nonneg _) hf hY hnext).1
  have hfinal : |law.expectationReal X| ≤ 6 * envelope time / L := by
    calc
      _ ≤ ((properPatternExtensions S.available Q U).card / target (time + 1)) *
          (C * e / (patternSurvivalSelectors Q S).card +
            |H| * (2 * L * e / 3) / ((patternSurvivalSelectors Q S).card * A) + tau / target time) := hraw
      _ ≤ ((properPatternExtensions S.available Q U).card / target (time + 1)) *
          (6 * (C + 2 * G) * e / (L * x) + tau / target time) :=
        mul_le_mul_of_nonneg_left (add_le_add hrate le_rfl) (by positivity)
      _ ≤ _ := pattern_relative_drift_envelope_budget C G e L x (envelope time) tau (target time)
        ((properPatternExtensions S.available Q U).card / target (time + 1))
        hC hG he hL hx hf htau hprefactor hcover hTaylorSmall
  have hcenter := centered_step_drift_nonpos law X sigma 0 (envelope (time + 1) - envelope time)
    0 (6 * envelope time / L) 0 hsigma (by simpa only [sub_zero] using hfinal)
    (by simp) (by simpa only [add_zero] using hgrowth)
  simpa only [patternRelativeCenteredObservable_increment, sub_zero] using hcenter

end

end Erdos207
