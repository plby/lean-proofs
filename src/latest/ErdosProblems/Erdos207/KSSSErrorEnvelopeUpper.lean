/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InversePowerStepUpper
import ErdosProblems.Erdos207.KSSSErrorEnvelopeGrowth

/-! # Upper discrete error-envelope increments before the residual clock reaches six -/

namespace Erdos207

noncomputable section

theorem ksssErrorEnvelope_unitStep_abs_upper
    (E₀ scale t : ℝ) (B : ℕ) (hE : 0 < E₀) (hs : 0 ≤ scale)
    (hclock : 3 * t + 6 ≤ E₀) :
    |ksssErrorEnvelope E₀ scale B (t + 1) - ksssErrorEnvelope E₀ scale B t| ≤
      (6 * (B : ℝ) * 2 ^ B) * ksssErrorEnvelope E₀ scale B t /
        (E₀ * ksssEdgeDensity E₀ t) := by
  have hp := ksssEdgeDensity_pos hE (show 3 * t < E₀ by linarith)
  have hq := ksssEdgeDensity_pos hE (show 3 * (t + 1) < E₀ by linarith)
  have hgap := ksssEdgeDensity_unitStep_difference E₀ t
  have hqp : ksssEdgeDensity E₀ (t + 1) ≤ ksssEdgeDensity E₀ t := by
    have hnonneg : 0 ≤ 3 / E₀ := by positivity
    linarith only [hgap, hnonneg]
  have hmargin : 6 ≤ E₀ * ksssEdgeDensity E₀ t := by
    have hid : E₀ * ksssEdgeDensity E₀ t = E₀ - 3 * t := by
      unfold ksssEdgeDensity
      field_simp
    rw [hid]
    linarith
  have hg : E₀ * (ksssEdgeDensity E₀ t - ksssEdgeDensity E₀ (t + 1)) = 3 := by
    rw [hgap]
    field_simp
  have hpq : ksssEdgeDensity E₀ t ≤ 2 * ksssEdgeDensity E₀ (t + 1) := by
    apply (mul_le_mul_iff_left₀ hE).mp
    nlinarith only [hg, hmargin]
  have h := inverse_power_step_abs_upper scale (ksssEdgeDensity E₀ t)
    (ksssEdgeDensity E₀ (t + 1)) B hs hq hqp hpq
  rw [hgap] at h
  convert h using 1 <;> dsimp only [ksssErrorEnvelope] <;> ring

theorem ksssConfigurationErrorEnvelope_unitStep_abs_upper
    (E₀ A₀ scale t : ℝ) (B z : ℕ) (hE : 0 < E₀) (hA : 0 ≤ A₀) (hs : 0 ≤ scale)
    (hclock : 3 * t + 6 ≤ E₀) (hB : 2 * z ≤ B) :
    |ksssConfigurationErrorEnvelope E₀ A₀ scale B z (t + 1) -
      ksssConfigurationErrorEnvelope E₀ A₀ scale B z t| ≤
      (6 * (B : ℝ) * 2 ^ B) * ksssConfigurationErrorEnvelope E₀ A₀ scale B z t /
        (E₀ * ksssEdgeDensity E₀ t) := by
  have hp := ksssEdgeDensity_pos hE (show 3 * t < E₀ by linarith)
  have hq := ksssEdgeDensity_pos hE (show 3 * (t + 1) < E₀ by linarith)
  rw [ksssConfigurationErrorEnvelope_eq_inverse E₀ A₀ scale t B z hp.ne' hB,
    ksssConfigurationErrorEnvelope_eq_inverse E₀ A₀ scale (t + 1) B z hq.ne' hB]
  have hb : ((B - 2 * z : ℕ) : ℝ) ≤ B := by exact_mod_cast Nat.sub_le B (2 * z)
  have hpow : (2 : ℝ) ^ (B - 2 * z) ≤ 2 ^ B :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le B (2 * z))
  have hcoef : 6 * ((B - 2 * z : ℕ) : ℝ) * (2 : ℝ) ^ (B - 2 * z) ≤ 6 * B * 2 ^ B := by
    gcongr
  have he : 0 ≤ ksssErrorEnvelope E₀ (scale * (A₀ / E₀) ^ z) (B - 2 * z) t := by
    unfold ksssErrorEnvelope
    positivity
  exact (ksssErrorEnvelope_unitStep_abs_upper E₀ (scale * (A₀ / E₀) ^ z) t (B - 2 * z) hE
    (by positivity) hclock).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef he) (mul_nonneg hE.le hp.le))

end

end Erdos207
