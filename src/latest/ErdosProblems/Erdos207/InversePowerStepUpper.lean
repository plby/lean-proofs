/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Tactic

/-! # A uniform upper bound for an inverse-power increment -/

namespace Erdos207

theorem inverse_power_step_abs_upper
    (s p q : ℝ) (B : ℕ) (hs : 0 ≤ s) (hq : 0 < q) (hqp : q ≤ p) (hpq : p ≤ 2 * q) :
    |s / q ^ B - s / p ^ B| ≤
      2 * (B : ℝ) * 2 ^ B * ((p - q) / p) * (s / p ^ B) := by
  have hp : 0 < p := hq.trans_le hqp
  have hr1 : 1 ≤ p / q := (le_div_iff₀ hq).mpr (by simpa using hqp)
  have hr2 : p / q ≤ 2 := (div_le_iff₀ hq).mpr hpq
  have hr0 : 0 ≤ p / q := div_nonneg hp.le hq.le
  have hpow : (p / q) ^ (B - 1) ≤ (2 : ℝ) ^ B :=
    (pow_le_pow_left₀ hr0 hr2 _).trans
      (pow_le_pow_right₀ (by norm_num) (Nat.sub_le B 1))
  have hdiff := abs_pow_sub_pow_le (a := p / q) (b := (1 : ℝ)) (n := B)
  rw [one_pow, abs_of_nonneg (sub_nonneg.mpr hr1), abs_of_nonneg hr0,
    abs_one, max_eq_left hr1] at hdiff
  have hdiff' : |(p / q) ^ B - 1| ≤ (p / q - 1) * (B : ℝ) * 2 ^ B :=
    hdiff.trans (mul_le_mul_of_nonneg_left hpow (mul_nonneg (sub_nonneg.mpr hr1) (Nat.cast_nonneg B)))
  have hgap : p / q - 1 ≤ 2 * ((p - q) / p) := by
    have hid : p / q - 1 = (p - q) / q := by field_simp <;> ring
    rw [hid]
    have hqhalf : 0 < p / 2 := by positivity
    calc
      (p - q) / q ≤ (p - q) / (p / 2) :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr hqp) hqhalf (by linarith)
      _ = _ := by ring
  have hid : s / q ^ B - s / p ^ B = (s / p ^ B) * ((p / q) ^ B - 1) := by
    rw [div_pow]
    field_simp
    <;> ring
  rw [hid, abs_mul, abs_of_nonneg (div_nonneg hs (pow_nonneg hp.le B))]
  calc
    _ ≤ (s / p ^ B) * ((p / q - 1) * (B : ℝ) * 2 ^ B) :=
      mul_le_mul_of_nonneg_left hdiff' (by positivity)
    _ ≤ (s / p ^ B) * ((2 * ((p - q) / p)) * (B : ℝ) * 2 ^ B) := by gcongr
    _ = _ := by ring

end Erdos207
