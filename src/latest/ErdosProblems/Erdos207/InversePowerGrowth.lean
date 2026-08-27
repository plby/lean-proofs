/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

/-! # A direct Bernoulli lower bound for inverse-power increments -/

namespace Erdos207

theorem inverse_power_step_growth
    (s p q : ℝ) (B : ℕ) (hs : 0 ≤ s) (hq : 0 < q) (hqp : q ≤ p) :
    (B : ℝ) * (p - q) / p * (s / p ^ B) ≤ s / q ^ B - s / p ^ B := by
  have hp : 0 < p := hq.trans_le hqp
  have hratio : -1 ≤ p / q := (by norm_num : (-1 : ℝ) ≤ 0).trans (div_nonneg hp.le hq.le)
  have hgap : (p - q) / p ≤ p / q - 1 := by
    rw [div_sub_one hq.ne']
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hqp) hq hqp
  have hbern : 1 + (B : ℝ) * ((p - q) / p) ≤ (p / q) ^ B :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg B))).trans
      (one_add_mul_sub_le_pow hratio B)
  have hid : (s / p ^ B) * (p / q) ^ B = s / q ^ B := by
    rw [div_pow]
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hbern (div_nonneg hs (pow_nonneg hp.le B))
  rw [hid] at hmul
  calc
    _ = (s / p ^ B) * (1 + (B : ℝ) * ((p - q) / p)) - s / p ^ B := by ring
    _ ≤ _ := sub_le_sub_right hmul _

theorem inverse_power_rescaling
    (s p r : ℝ) (B z : ℕ) (hp : p ≠ 0) (hB : 2 * z ≤ B) :
    (s / p ^ B) * (p ^ 2 * r) ^ z = s * r ^ z / p ^ (B - 2 * z) := by
  have he : B = (B - 2 * z) + 2 * z := by omega
  rw [mul_pow, ← pow_mul, he, pow_add]
  field_simp
  simp only [Nat.add_sub_cancel]
  ring

end Erdos207
