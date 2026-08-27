/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationHazardScale

/-! # An explicit scalar sufficient condition for forbidden-family density -/

namespace Erdos207

open scoped NNReal

theorem regularization_density_of_power_bound
    (m k : ℕ) (hk : 2 ≤ k) (hm : 2 * (k - 1) ≤ m) (n sigma C D : ℝ≥0)
    (hn : 0 < n) (hsigma : 0 < sigma) (hC : 0 < C)
    (hmass : sigma * n ^ 3 / C ≤ m) (hD : D ≤ 9 * n ^ (3 * k - 4))
    (hbudget : 324 * (2 : ℝ≥0) ^ k * (2 * C) ^ (k - 1) * (k - 1).factorial ≤ sigma ^ (k - 1) * n) :
    (2 : ℝ≥0) ^ k * D ≤ (1 / 36 : ℝ≥0) * Nat.choose m (k - 1) := by
  have hlow := regularization_choose_lower m (k - 1) hm (sigma * n ^ 3 / C) hmass
  apply le_trans _ (mul_le_mul_of_nonneg_left hlow (show (0 : ℝ≥0) ≤ 1 / 36 from zero_le))
  have hnormalize : (1 / 36 : ℝ≥0) * ((sigma * n ^ 3 / C / 2) ^ (k - 1) / (k - 1).factorial) =
      (sigma ^ (k - 1) * n ^ (3 * (k - 1))) /
        (36 * (2 * C) ^ (k - 1) * (k - 1).factorial) := by
    have hC0 := ne_of_gt hC
    have hf0 : ((k - 1).factorial : ℝ≥0) ≠ 0 := by exact_mod_cast (k - 1).factorial_ne_zero
    simp only [div_pow, mul_pow, pow_mul]
    field_simp
  rw [hnormalize]
  have hden : (0 : ℝ≥0) < 36 * (2 * C) ^ (k - 1) * (k - 1).factorial := by positivity
  apply (le_div_iff₀ hden).mpr
  calc
    _ ≤ ((2 : ℝ≥0) ^ k * (9 * n ^ (3 * k - 4))) *
        (36 * (2 * C) ^ (k - 1) * (k - 1).factorial) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD zero_le) zero_le
    _ = (324 * (2 : ℝ≥0) ^ k * (2 * C) ^ (k - 1) * (k - 1).factorial) * n ^ (3 * k - 4) := by ring
    _ ≤ (sigma ^ (k - 1) * n) * n ^ (3 * k - 4) := mul_le_mul_of_nonneg_right hbudget zero_le
    _ = _ := by
      rw [mul_assoc, ← pow_succ']
      have he : 3 * k - 4 + 1 = 3 * (k - 1) := by omega
      rw [he]

end Erdos207
