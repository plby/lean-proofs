/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InversePowerGrowth
import ErdosProblems.Erdos207.KSSSTrajectories

/-! # Direct discrete growth of the source error envelopes -/

namespace Erdos207

noncomputable section

def ksssErrorEnvelope (E₀ scale : ℝ) (B : ℕ) (t : ℝ) : ℝ :=
  scale / ksssEdgeDensity E₀ t ^ B

/-- Here `z` is the source's `j - 4 - c`. -/
def ksssConfigurationErrorEnvelope (E₀ A₀ scale : ℝ) (B z : ℕ) (t : ℝ) : ℝ :=
  ksssErrorEnvelope E₀ scale B t * (ksssEdgeDensity E₀ t ^ 2 * A₀ / E₀) ^ z

theorem ksssEdgeDensity_unitStep_difference (E₀ t : ℝ) :
    ksssEdgeDensity E₀ t - ksssEdgeDensity E₀ (t + 1) = 3 / E₀ := by
  dsimp only [ksssEdgeDensity]
  ring

theorem ksssErrorEnvelope_unitStep_growth
    (E₀ scale t : ℝ) (B : ℕ) (hE : 0 < E₀) (hs : 0 ≤ scale)
    (hclock : 3 * (t + 1) < E₀) :
    3 * (B : ℝ) * ksssErrorEnvelope E₀ scale B t / (E₀ * ksssEdgeDensity E₀ t) ≤
      ksssErrorEnvelope E₀ scale B (t + 1) - ksssErrorEnvelope E₀ scale B t := by
  have hq := ksssEdgeDensity_pos hE hclock
  have hgap := ksssEdgeDensity_unitStep_difference E₀ t
  have hqp : ksssEdgeDensity E₀ (t + 1) ≤ ksssEdgeDensity E₀ t := by
    have hd : 0 ≤ 3 / E₀ := div_nonneg (by norm_num) hE.le
    linarith
  have h := inverse_power_step_growth scale (ksssEdgeDensity E₀ t)
    (ksssEdgeDensity E₀ (t + 1)) B hs hq hqp
  rw [hgap] at h
  convert h using 1 <;> dsimp only [ksssErrorEnvelope] <;> ring

theorem ksssConfigurationErrorEnvelope_eq_inverse
    (E₀ A₀ scale t : ℝ) (B z : ℕ) (hp : ksssEdgeDensity E₀ t ≠ 0) (hB : 2 * z ≤ B) :
    ksssConfigurationErrorEnvelope E₀ A₀ scale B z t =
      ksssErrorEnvelope E₀ (scale * (A₀ / E₀) ^ z) (B - 2 * z) t := by
  unfold ksssConfigurationErrorEnvelope ksssErrorEnvelope
  rw [show ksssEdgeDensity E₀ t ^ 2 * A₀ / E₀ =
    ksssEdgeDensity E₀ t ^ 2 * (A₀ / E₀) by ring]
  exact inverse_power_rescaling scale (ksssEdgeDensity E₀ t) (A₀ / E₀) B z hp hB

theorem ksssConfigurationErrorEnvelope_unitStep_growth
    (E₀ A₀ scale t : ℝ) (B z : ℕ) (hE : 0 < E₀) (hA : 0 ≤ A₀) (hs : 0 ≤ scale)
    (hclock : 3 * (t + 1) < E₀) (hB : 2 * z ≤ B) :
    3 * ((B - 2 * z : ℕ) : ℝ) * ksssConfigurationErrorEnvelope E₀ A₀ scale B z t /
      (E₀ * ksssEdgeDensity E₀ t) ≤
        ksssConfigurationErrorEnvelope E₀ A₀ scale B z (t + 1) -
          ksssConfigurationErrorEnvelope E₀ A₀ scale B z t := by
  have hp := ksssEdgeDensity_pos hE (show 3 * t < E₀ by linarith)
  have hq := ksssEdgeDensity_pos hE hclock
  rw [ksssConfigurationErrorEnvelope_eq_inverse E₀ A₀ scale t B z hp.ne' hB,
    ksssConfigurationErrorEnvelope_eq_inverse E₀ A₀ scale (t + 1) B z hq.ne' hB]
  exact ksssErrorEnvelope_unitStep_growth E₀ (scale * (A₀ / E₀) ^ z) t (B - 2 * z) hE
    (mul_nonneg hs (pow_nonneg (div_nonneg hA hE.le) z)) hclock

theorem ksssConfigurationErrorEnvelope_unitStep_growth_half
    (E₀ A₀ scale t : ℝ) (B z : ℕ) (hE : 0 < E₀) (hA : 0 ≤ A₀) (hs : 0 ≤ scale)
    (hclock : 3 * (t + 1) < E₀) (hB : 4 * z ≤ B) :
    (3 * (B : ℝ) / 2) * ksssConfigurationErrorEnvelope E₀ A₀ scale B z t /
      (E₀ * ksssEdgeDensity E₀ t) ≤
        ksssConfigurationErrorEnvelope E₀ A₀ scale B z (t + 1) -
          ksssConfigurationErrorEnvelope E₀ A₀ scale B z t := by
  have hp := ksssEdgeDensity_pos hE (show 3 * t < E₀ by linarith)
  have hb : (B : ℝ) ≤ 2 * ((B - 2 * z : ℕ) : ℝ) := by
    exact_mod_cast (show B ≤ 2 * (B - 2 * z) by omega)
  have hcoef : 3 * (B : ℝ) / 2 ≤ 3 * ((B - 2 * z : ℕ) : ℝ) := by linarith
  have he : 0 ≤ ksssConfigurationErrorEnvelope E₀ A₀ scale B z t := by
    unfold ksssConfigurationErrorEnvelope ksssErrorEnvelope
    positivity
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef he) (mul_nonneg hE.le hp.le)).trans
    (ksssConfigurationErrorEnvelope_unitStep_growth E₀ A₀ scale t B z hE hA hs hclock (by omega))

end

end Erdos207
