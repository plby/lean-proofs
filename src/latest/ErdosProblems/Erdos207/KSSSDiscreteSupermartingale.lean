/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSTaylorSourceScale
import ErdosProblems.Erdos207.CenteredStepBounds

/-! # Nonpositive centered drift from the explicit source-scale budgets -/

namespace Erdos207

noncomputable section

theorem ksss_pair_centered_step_drift_nonpos
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E₀ A₀ scale t σ D : ℝ) (B : ℕ)
    (hσ : |σ| = 1) (hE : 0 < E₀) (hA : 0 ≤ A₀) (hs : 0 ≤ scale) (ht : 0 ≤ t)
    (hclock : 3 * (t + 1) < E₀) (hsize : A₀ ≤ scale * E₀ ^ 2)
    (horders : ∀ d ∈ orders, 1 ≤ d) (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hab : ∀ d ∈ orders, a d * E₀ ^ d ≤ b d)
    (hraw : |μ.expectationReal X - ksssPairSlope orders a E₀ A₀ t| ≤
      D * ksssErrorEnvelope E₀ scale B t / (E₀ * ksssEdgeDensity E₀ t))
    (hbudget : D + ksssPairTaylorCoefficient orders b ≤ 3 * (B : ℝ)) :
    μ.expectationReal (fun ω ↦
      σ * (X ω - (ksssPairTrajectory orders a E₀ A₀ (t + 1) -
        ksssPairTrajectory orders a E₀ A₀ t)) -
          (ksssErrorEnvelope E₀ scale B (t + 1) - ksssErrorEnvelope E₀ scale B t)) ≤ 0 := by
  have hp := ksssEdgeDensity_pos hE (show 3 * t < E₀ by linarith)
  have he : 0 ≤ ksssErrorEnvelope E₀ scale B t := by unfold ksssErrorEnvelope; positivity
  apply centered_step_drift_nonpos μ X σ _ _ (ksssPairSlope orders a E₀ A₀ t)
    (D * ksssErrorEnvelope E₀ scale B t / (E₀ * ksssEdgeDensity E₀ t))
    (ksssPairTaylorCoefficient orders b * ksssErrorEnvelope E₀ scale B t /
      (E₀ * ksssEdgeDensity E₀ t)) hσ hraw
    (ksssPairTrajectory_unitStep_error_source_scale orders a b E₀ A₀ scale t B
      hE hA hs ht hclock hsize horders ha hab)
  calc
    _ = (D + ksssPairTaylorCoefficient orders b) * ksssErrorEnvelope E₀ scale B t /
        (E₀ * ksssEdgeDensity E₀ t) := by ring
    _ ≤ 3 * (B : ℝ) * ksssErrorEnvelope E₀ scale B t / (E₀ * ksssEdgeDensity E₀ t) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbudget he) (mul_nonneg hE.le hp.le)
    _ ≤ _ := ksssErrorEnvelope_unitStep_growth E₀ scale t B hE hs hclock

theorem ksss_configuration_centered_step_drift_nonpos
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E₀ A₀ scale t σ D : ℝ) (B d c : ℕ)
    (hσ : |σ| = 1) (hd : d ∈ orders) (hc : c < d) (hB : 4 * (d - c - 1) ≤ B)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (hs : 0 ≤ scale) (ht : 0 ≤ t)
    (hclock : 3 * (t + 1) < E₀) (hsize : A₀ ≤ scale * E₀ ^ 2)
    (horders : ∀ k ∈ orders, 1 ≤ k) (ha : ∀ k ∈ orders, 0 ≤ a k)
    (hab : ∀ k ∈ orders, a k * E₀ ^ k ≤ b k)
    (hraw : |μ.expectationReal X - ksssConfigurationSlope orders a E₀ A₀ d c t| ≤
      D * ksssConfigurationErrorEnvelope E₀ A₀ scale B (d - c - 1) t /
        (E₀ * ksssEdgeDensity E₀ t))
    (hbudget : D + ksssConfigurationTaylorCoefficient orders b d c ≤ 3 * (B : ℝ) / 2) :
    μ.expectationReal (fun ω ↦
      σ * (X ω - (ksssConfigurationTrajectory orders a E₀ A₀ d c (t + 1) -
        ksssConfigurationTrajectory orders a E₀ A₀ d c t)) -
          (ksssConfigurationErrorEnvelope E₀ A₀ scale B (d - c - 1) (t + 1) -
            ksssConfigurationErrorEnvelope E₀ A₀ scale B (d - c - 1) t)) ≤ 0 := by
  have hp := ksssEdgeDensity_pos hE (show 3 * t < E₀ by linarith)
  have he : 0 ≤ ksssConfigurationErrorEnvelope E₀ A₀ scale B (d - c - 1) t := by
    unfold ksssConfigurationErrorEnvelope ksssErrorEnvelope
    positivity
  apply centered_step_drift_nonpos μ X σ _ _ (ksssConfigurationSlope orders a E₀ A₀ d c t)
    (D * ksssConfigurationErrorEnvelope E₀ A₀ scale B (d - c - 1) t / (E₀ * ksssEdgeDensity E₀ t))
    (ksssConfigurationTaylorCoefficient orders b d c *
      ksssConfigurationErrorEnvelope E₀ A₀ scale B (d - c - 1) t / (E₀ * ksssEdgeDensity E₀ t)) hσ hraw
    (ksssConfigurationTrajectory_unitStep_error_source_scale orders a b E₀ A₀ scale t B d c
      hd hc (by omega) hE hA hs ht hclock hsize horders ha hab)
  calc
    _ = (D + ksssConfigurationTaylorCoefficient orders b d c) *
        ksssConfigurationErrorEnvelope E₀ A₀ scale B (d - c - 1) t / (E₀ * ksssEdgeDensity E₀ t) := by ring
    _ ≤ (3 * (B : ℝ) / 2) * ksssConfigurationErrorEnvelope E₀ A₀ scale B (d - c - 1) t /
        (E₀ * ksssEdgeDensity E₀ t) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbudget he) (mul_nonneg hE.le hp.le)
    _ ≤ _ := ksssConfigurationErrorEnvelope_unitStep_growth_half E₀ A₀ scale t B (d - c - 1)
      hE hA hs hclock hB

end

end Erdos207
