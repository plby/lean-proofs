/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativePatternEnvelope
import ErdosProblems.Erdos207.SharpTransferConstant

/-! # Explicit fine-scale budgets for the rounded initial survival schedules -/

namespace Erdos207

noncomputable section

theorem ksss_pair_relative_error_fine
    (E N t time x : ℝ) (b B : ℕ) (hN : 0 < N) (ht : 0 < t)
    (hfloor : 1 / t ^ b ≤ ksssEdgeDensity E time)
    (hx : N / (2 * t) * ksssEdgeDensity E time ^ 2 ≤ x) :
    ksssErrorEnvelope E (N / t ^ ksssPowerErrorExponent b B) B time ≤
      (2 / t ^ (b + 1)) * x := by
  have hp : 0 < ksssEdgeDensity E time := (by positivity : 0 < 1 / t ^ b).trans_le hfloor
  have hxpos : 0 < x := (by positivity : 0 < N / (2 * t) * ksssEdgeDensity E time ^ 2).trans_le hx
  have hratio := (relativePatternEnvelope_pair_error E N t time x (ksssPowerErrorExponent b B) B
    hN ht hp hx).trans (relativePatternEnvelope_terminal_bound E t time b B ht hfloor)
  have hbound : ksssErrorEnvelope E (N / t ^ ksssPowerErrorExponent b B) B time / x ≤
      (16 / t ^ b) / (8 * t) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * t)).mpr
    convert hratio using 1 <;> ring
  have heq : (16 / t ^ b) / (8 * t) = 2 / t ^ (b + 1) := by rw [pow_succ]; ring
  rw [heq] at hbound
  exact (div_le_iff₀ hxpos).mp hbound

theorem sharp_power_rounding_budgets
    (t x L : ℝ) (b : ℕ) (ht : 32 ≤ t)
    (hx : t ^ (b + 3) ≤ x) (hL : t ^ 2 ≤ L) :
    0 ≤ 16 / t ^ (b + 1) ∧ 16 / t ^ (b + 1) ≤ 1 / 2 ∧
      3 * t + 2 ≤ (16 / t ^ (b + 1)) * x / 8 ∧
      18 * t ≤ L ∧ 16 / t ^ (b + 1) ≤ 1 / t ^ b ∧ 32 ≤ x := by
  have htpos : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hpow : t ≤ t ^ (b + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ ht1 (by omega : 1 ≤ b + 1)
  have hpowx : t ≤ t ^ (b + 3) := by
    simpa only [pow_one] using pow_le_pow_right₀ ht1 (by omega : 1 ≤ b + 3)
  refine ⟨by positivity, ?_, ?_, ?_, ?_, ht.trans (hpowx.trans hx)⟩
  · apply (div_le_iff₀ (pow_pos htpos _)).mpr
    linarith only [hpow, ht]
  · calc
      3 * t + 2 ≤ 2 * t ^ 2 := by nlinarith only [ht]
      _ = (16 / t ^ (b + 1)) * t ^ (b + 3) / 8 := by
        rw [show b + 3 = (b + 1) + 2 by omega, pow_add]
        field_simp
        ring
      _ ≤ _ := by gcongr
  · exact (show 18 * t ≤ t ^ 2 by nlinarith only [ht]).trans hL
  · rw [pow_succ]
    apply (div_le_div_iff₀ (by positivity : 0 < t ^ b * t) (pow_pos htpos b)).mpr
    have h := mul_le_mul_of_nonneg_left (show 16 ≤ t by linarith) (pow_nonneg htpos.le b)
    nlinarith only [h]

end

end Erdos207
