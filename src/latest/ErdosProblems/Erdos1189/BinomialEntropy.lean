/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The logarithmic cost of requiring distinct unordered profiles.
Informal argument: a coarse falling-factorial bound, sufficient for an O(k log k) loss.
Formal author: OpenAI Codex.
-/

import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Erdos1189

lemma pow_le_choose_mul_pow {B r : ℕ} (hr : 1 ≤ r) (hBr : r ≤ B) :
    B ^ r ≤ r ^ (2 * r) * B.choose r := by
  let L := B + 1 - r
  have hL : L + r = B + 1 := Nat.sub_add_cancel (by omega)
  have hL1 : 1 ≤ L := by omega
  have hBL : B ≤ r * L := by
    have h := Nat.mul_le_mul_left (L - 1) hr
    have hLsub : L - 1 + 1 = L := by omega
    nlinarith
  have hLpow : L ^ r ≤ r ^ r * B.choose r := by
    calc
      _ ≤ B.descFactorial r := Nat.pow_sub_le_descFactorial B r
      _ = r.factorial * B.choose r := Nat.descFactorial_eq_factorial_mul_choose B r
      _ ≤ r ^ r * B.choose r := Nat.mul_le_mul_right _ (Nat.factorial_le_pow r)
  calc
    B ^ r ≤ (r * L) ^ r := Nat.pow_le_pow_left hBL r
    _ = r ^ r * L ^ r := Nat.mul_pow r L r
    _ ≤ r ^ r * (r ^ r * B.choose r) := Nat.mul_le_mul_left _ hLpow
    _ = r ^ (2 * r) * B.choose r := by rw [two_mul, pow_add]; ring

theorem log_choose_lower {B r : ℕ} (hr : 1 ≤ r) (hBr : r ≤ B) :
    (r : ℝ) * Real.log B - 2 * r * Real.log r ≤ Real.log (B.choose r) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hc0 : (0 : ℝ) < B.choose r := by exact_mod_cast Nat.choose_pos hBr
  have hpow : (B : ℝ) ^ r ≤ (r : ℝ) ^ (2 * r) * B.choose r := by
    exact_mod_cast pow_le_choose_mul_pow hr hBr
  have hlog := Real.log_le_log (pow_pos hB0 r) hpow
  rw [Real.log_mul (pow_ne_zero _ hr0.ne') hc0.ne', Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  linarith

end Erdos1189
