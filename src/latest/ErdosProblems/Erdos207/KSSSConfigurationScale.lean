/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSSourceNormalization
import ErdosProblems.Erdos207.KSSSErrorEnvelopeGrowth
import ErdosProblems.Erdos207.ConfigurationProductBudget

/-! # The source configuration scale and its trajectory bounds -/

namespace Erdos207

open Finset

noncomputable section

def ksssConfigurationScale (E₀ A₀ t : ℝ) : ℝ :=
  ksssEdgeDensity E₀ t ^ 2 * A₀ / E₀

theorem ksssConfigurationScale_nonneg
    {E₀ A₀ t : ℝ} (hE : 0 < E₀) (hA : 0 ≤ A₀) :
    0 ≤ ksssConfigurationScale E₀ A₀ t := by
  unfold ksssConfigurationScale
  positivity

theorem ksssAvailableTrajectory_le_clock_mul_scale
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (ht : 0 ≤ t) (hclock : 3 * t < E₀)
    (ha : ∀ d ∈ orders, 0 ≤ a d) :
    ksssAvailableTrajectory orders a E₀ A₀ t ≤ E₀ * ksssConfigurationScale E₀ A₀ t := by
  have hp := (ksssEdgeDensity_pos hE hclock).le
  have hp1 := ksssEdgeDensity_le_one hE ht
  have hrho := ksssPoissonExponent_nonneg orders a ha ht
  have hexp : Real.exp (-ksssPoissonExponent orders a t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hrho)
  have hp3 : ksssEdgeDensity E₀ t ^ 3 ≤ ksssEdgeDensity E₀ t ^ 2 := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (sq_nonneg _) hp1
  calc
    _ ≤ A₀ * ksssEdgeDensity E₀ t ^ 3 :=
      mul_le_of_le_one_right (mul_nonneg hA (pow_nonneg hp _)) hexp
    _ ≤ A₀ * ksssEdgeDensity E₀ t ^ 2 := mul_le_mul_of_nonneg_left hp3 hA
    _ = _ := by unfold ksssConfigurationScale; field_simp

theorem ksssConfigurationScale_le_pair
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E₀ A₀ t : ℝ)
    (hE : 0 < E₀) (hA : 0 < A₀) (ht : 0 ≤ t) (hclock : 3 * t < E₀)
    (ha : ∀ d ∈ orders, 0 ≤ a d) (hab : ∀ d ∈ orders, a d * E₀ ^ d ≤ b d) :
    ksssConfigurationScale E₀ A₀ t ≤
      (Real.exp (∑ d ∈ orders, b d) / 3) * ksssPairTrajectory orders a E₀ A₀ t := by
  have hp := ksssEdgeDensity_pos hE hclock
  have hx := ksssPairTrajectory_pos orders a hE hA hclock
  have hrho := ksssPoissonExponent_le_sum orders a b ha hab ht (by linarith)
  have hid : (Real.exp (ksssPoissonExponent orders a t) / 3) *
      ksssPairTrajectory orders a E₀ A₀ t = ksssConfigurationScale E₀ A₀ t := by
    rw [ksssPairTrajectory_source orders a E₀ A₀ t hE.ne' hp.ne', Real.exp_neg]
    unfold ksssConfigurationScale
    field_simp
  rw [← hid]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hrho) (by norm_num)) hx.le

theorem ksssConfigurationTrajectory_nonneg
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ) (d c : ℕ)
    (hA : 0 ≤ A₀) (ht : 0 ≤ t) (hp : 0 ≤ ksssEdgeDensity E₀ t) (ha : 0 ≤ a d) :
    0 ≤ ksssConfigurationTrajectory orders a E₀ A₀ d c t := by
  unfold ksssConfigurationTrajectory ksssAvailableTrajectory
  positivity

theorem ksssConfigurationTrajectory_le_scale
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E₀ A₀ t : ℝ) (d c : ℕ)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (ht : 0 ≤ t) (hclock : 3 * t < E₀)
    (ha : ∀ k ∈ orders, 0 ≤ a k) (had : 0 ≤ a d)
    (hab : a d * E₀ ^ d ≤ b d) (hcd : c ≤ d) :
    ksssConfigurationTrajectory orders a E₀ A₀ d c t ≤
      (d.choose c : ℝ) * b d * ksssConfigurationScale E₀ A₀ t ^ (d - c) := by
  have hp := (ksssEdgeDensity_pos hE hclock).le
  have hAvail : 0 ≤ ksssAvailableTrajectory orders a E₀ A₀ t := by
    unfold ksssAvailableTrajectory
    positivity
  exact configuration_monomial_le d c hcd had ht (by linarith) hAvail
    (ksssAvailableTrajectory_le_clock_mul_scale orders a E₀ A₀ t hE hA ht hclock ha)
    (ksssConfigurationScale_nonneg hE hA) hab

theorem ksssConfigurationErrorEnvelope_scale
    (E₀ A₀ scale t : ℝ) (B z : ℕ) :
    ksssConfigurationErrorEnvelope E₀ A₀ scale B z t =
      ksssErrorEnvelope E₀ scale B t * ksssConfigurationScale E₀ A₀ t ^ z := rfl

end

end Erdos207
