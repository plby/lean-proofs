/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSConfigurationScale

/-! # Lower error-envelope scales and the curvature absorption inequality -/

namespace Erdos207

noncomputable section

theorem ksssErrorEnvelope_ge_scale
    (E₀ scale t : ℝ) (B : ℕ) (hE : 0 < E₀) (hs : 0 ≤ scale)
    (ht : 0 ≤ t) (hclock : 3 * t < E₀) :
    scale ≤ ksssErrorEnvelope E₀ scale B t := by
  have hp := ksssEdgeDensity_pos hE hclock
  have hp1 := ksssEdgeDensity_le_one hE ht
  have hb : ksssEdgeDensity E₀ t ^ B ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hp.le hp1 B
  apply (le_div_iff₀ (pow_pos hp B)).mpr
  exact mul_le_of_le_one_right hs hb

theorem ksssConfigurationErrorEnvelope_ge_scale
    (E₀ A₀ scale t : ℝ) (B z : ℕ)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (hs : 0 ≤ scale)
    (ht : 0 ≤ t) (hclock : 3 * t < E₀) (hB : 2 * z ≤ B) :
    scale * (A₀ / E₀) ^ z ≤ ksssConfigurationErrorEnvelope E₀ A₀ scale B z t := by
  rw [ksssConfigurationErrorEnvelope_eq_inverse E₀ A₀ scale t B z
    (ksssEdgeDensity_pos hE hclock).ne' hB]
  exact ksssErrorEnvelope_ge_scale E₀ (scale * (A₀ / E₀) ^ z) t (B - 2 * z) hE
    (by positivity) ht hclock

theorem ksss_curvature_scale_le_configuration_error
    (E₀ A₀ scale t : ℝ) (B z : ℕ)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (hs : 0 ≤ scale)
    (ht : 0 ≤ t) (hclock : 3 * t < E₀) (hB : 2 * z ≤ B)
    (hsize : A₀ ≤ scale * E₀ ^ 2) :
    A₀ ^ (z + 1) / E₀ ^ (z + 3) ≤
      ksssConfigurationErrorEnvelope E₀ A₀ scale B z t / (E₀ * ksssEdgeDensity E₀ t) := by
  have hp := ksssEdgeDensity_pos hE hclock
  have hp1 := ksssEdgeDensity_le_one hE ht
  have he := ksssConfigurationErrorEnvelope_ge_scale E₀ A₀ scale t B z hE hA hs ht hclock hB
  have hbase : A₀ / E₀ ^ 3 ≤ scale / E₀ := by
    rw [div_le_div_iff₀ (pow_pos hE 3) hE]
    have hm := mul_le_mul_of_nonneg_right hsize hE.le
    nlinarith only [hm]
  calc
    _ = (A₀ / E₀) ^ z * (A₀ / E₀ ^ 3) := by
      rw [pow_add, pow_succ, div_pow]
      field_simp <;> simp only [pow_add] <;> ring
    _ ≤ (A₀ / E₀) ^ z * (scale / E₀) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (scale * (A₀ / E₀) ^ z) / E₀ := by ring
    _ ≤ ksssConfigurationErrorEnvelope E₀ A₀ scale B z t / E₀ :=
      div_le_div_of_nonneg_right he hE.le
    _ ≤ ksssConfigurationErrorEnvelope E₀ A₀ scale B z t / (E₀ * ksssEdgeDensity E₀ t) := by
      apply div_le_div_of_nonneg_left ((by positivity : 0 ≤ scale * (A₀ / E₀) ^ z).trans he)
        (mul_pos hE hp)
      exact mul_le_of_le_one_right hE.le hp1

end

end Erdos207
