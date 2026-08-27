/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceNibbleTriangleRootBound

/-! # One explicit coefficient for all local-configuration root cases -/

namespace Erdos207

open scoped NNReal

noncomputable section

def sourceNibbleMomentCoefficient (ell q : ℕ) (w : ℝ≥0) : ℝ≥0 :=
  ((q + 1) ^ ell : ℕ) * (2 : ℝ≥0) ^ (q - 2) * w ^ q

theorem sourceNibbleMomentCoefficient_one_le (ell q : ℕ) (w : ℝ≥0) (hw : 1 ≤ w) :
    1 ≤ sourceNibbleMomentCoefficient ell q w := by
  apply one_le_mul_of_one_le_of_one_le
  · apply one_le_mul_of_one_le_of_one_le
    · exact_mod_cast (one_le_pow₀ (show 1 ≤ q + 1 by omega) : 1 ≤ (q + 1) ^ ell)
    · exact one_le_pow₀ (by norm_num : (1 : ℝ≥0) ≤ 2)
  · exact one_le_pow₀ hw

theorem sourceNibble_small_coefficient_le
    (ell q r a : ℕ) (hr : r ≤ q) (ha : a ≤ q - 2) (w b : ℝ≥0) (hw : 1 ≤ w) :
    ((r + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ a * b) * w ^ r ≤
      sourceNibbleMomentCoefficient ell q w * b := by
  have hc : (((r + 1) ^ ell : ℕ) : ℝ≥0) ≤ ((q + 1) ^ ell : ℕ) := by
    exact_mod_cast Nat.pow_le_pow_left (Nat.add_le_add_right hr 1) ell
  have htwo : (2 : ℝ≥0) ^ a ≤ 2 ^ (q - 2) := pow_le_pow_right₀ (by norm_num) ha
  have hwp : w ^ r ≤ w ^ q := pow_le_pow_right₀ hw hr
  calc
    _ = ((((r + 1) ^ ell : ℕ) : ℝ≥0) * (2 : ℝ≥0) ^ a * w ^ r) * b := by ring
    _ ≤ ((((q + 1) ^ ell : ℕ) : ℝ≥0) * (2 : ℝ≥0) ^ (q - 2) * w ^ q) * b :=
      mul_le_mul_of_nonneg_right (mul_le_mul' (mul_le_mul' hc htwo) hwp) zero_le
    _ = _ := rfl

theorem sourceNibble_nonempty_scale_le
    (n C y z p : ℝ≥0) (j : ℕ) (hj : 4 ≤ j)
    (hz : z ≤ y * p ^ (3 * (j - 3)) * n) :
    C * z * n ^ (j - 4) ≤ C * y * p ^ (3 * (j - 3)) * n ^ (j - 3) := by
  calc
    _ ≤ C * (y * p ^ (3 * (j - 3)) * n) * n ^ (j - 4) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz zero_le) zero_le
    _ = _ := by
      have he : j - 3 = (j - 4) + 1 := by omega
      rw [he, pow_succ]
      ring

end

end Erdos207
