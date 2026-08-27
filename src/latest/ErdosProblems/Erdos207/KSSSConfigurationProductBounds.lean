/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSConfigurationScale

/-! # Coefficient-explicit trajectory/error product inequalities -/

namespace Erdos207

open Finset

noncomputable section

theorem ksssConfigurationTrajectory_error_product
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E₀ A₀ scale t : ℝ) (B d c z r : ℕ)
    (hE : 0 < E₀) (hA : 0 < A₀) (hs : 0 ≤ scale) (ht : 0 ≤ t) (hclock : 3 * t < E₀)
    (ha : ∀ k ∈ orders, 0 ≤ a k) (hab : ∀ k ∈ orders, a k * E₀ ^ k ≤ b k)
    (hd : d ∈ orders) (hcd : c ≤ d) (hdegree : d - c = z + r) :
    ksssConfigurationTrajectory orders a E₀ A₀ d c t * ksssErrorEnvelope E₀ scale B t ≤
      ((d.choose c : ℝ) * b d) * (Real.exp (∑ k ∈ orders, b k) / 3) ^ r *
        ksssPairTrajectory orders a E₀ A₀ t ^ r *
          ksssConfigurationErrorEnvelope E₀ A₀ scale B z t := by
  have hp := ksssEdgeDensity_pos hE hclock
  have hx := ksssPairTrajectory_pos orders a hE hA hclock
  have hb : 0 ≤ b d := (mul_nonneg (ha d hd) (pow_nonneg hE.le d)).trans (hab d hd)
  have he : 0 ≤ ksssErrorEnvelope E₀ scale B t := by
    unfold ksssErrorEnvelope
    positivity
  have hy := ksssConfigurationTrajectory_le_scale orders a b E₀ A₀ t d c hE hA.le ht hclock
    ha (ha d hd) (hab d hd) hcd
  rw [hdegree] at hy
  exact power_scaled_error_product z r (by positivity)
    (ksssConfigurationScale_nonneg hE hA.le) (by positivity) hx.le he hy
    (ksssConfigurationScale_le_pair orders a b E₀ A₀ t hE hA ht hclock ha hab)

theorem ksssConfigurationErrorEnvelope_succ_scale
    (E₀ A₀ scale t : ℝ) (B z : ℕ) :
    ksssConfigurationErrorEnvelope E₀ A₀ scale B (z + 1) t =
      ksssConfigurationScale E₀ A₀ t *
        ksssConfigurationErrorEnvelope E₀ A₀ scale B z t := by
  rw [ksssConfigurationErrorEnvelope_scale, ksssConfigurationErrorEnvelope_scale, pow_succ]
  ring

theorem ksssConfigurationErrorEnvelope_succ_le_pair
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E₀ A₀ scale t : ℝ) (B z : ℕ)
    (hE : 0 < E₀) (hA : 0 < A₀) (hs : 0 ≤ scale) (ht : 0 ≤ t) (hclock : 3 * t < E₀)
    (ha : ∀ k ∈ orders, 0 ≤ a k) (hab : ∀ k ∈ orders, a k * E₀ ^ k ≤ b k) :
    ksssConfigurationErrorEnvelope E₀ A₀ scale B (z + 1) t ≤
      (Real.exp (∑ k ∈ orders, b k) / 3) * ksssPairTrajectory orders a E₀ A₀ t *
        ksssConfigurationErrorEnvelope E₀ A₀ scale B z t := by
  have hp := ksssEdgeDensity_pos hE hclock
  have he : 0 ≤ ksssConfigurationErrorEnvelope E₀ A₀ scale B z t := by
    unfold ksssConfigurationErrorEnvelope ksssErrorEnvelope
    positivity
  rw [ksssConfigurationErrorEnvelope_succ_scale]
  exact mul_le_mul_of_nonneg_right
    (ksssConfigurationScale_le_pair orders a b E₀ A₀ t hE hA ht hclock ha hab) he

end

end Erdos207
