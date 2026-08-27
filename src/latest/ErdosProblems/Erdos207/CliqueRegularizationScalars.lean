/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CliquePatternTypicality

/-! # Explicit scalar margins converting iteration typicality into regularizer inputs -/

namespace Erdos207

theorem small_clique_target_lower
    (p tau n : ℝ) (s : ℕ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (htau : 0 ≤ tau) (htau1 : tau ≤ 1) (hn : 0 ≤ n) (hs : s ≤ 4) :
    p ^ 4 * tau ^ 6 * n ≤ p ^ s * tau ^ (s.choose 2) * n := by
  have hchoose : s.choose 2 ≤ 6 := by
    simpa only [show (4 : ℕ).choose 2 = 6 by decide] using Nat.choose_le_choose 2 hs
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (pow_le_pow_of_le_one hp hp1 hs)
      (pow_le_pow_of_le_one htau htau1 hchoose) (pow_nonneg htau _) (pow_nonneg hp _)) hn

theorem proper_clique_error_two_sided
    (actual target xi : ℝ) (s : ℕ) (htarget : 16 ≤ target)
    (hxi : xi ≤ 1 / 4) (hs : s ≤ 4)
    (herr : |actual - target| ≤ xi * target + s) :
    target / 2 ≤ actual ∧ actual ≤ 2 * target := by
  have htarget0 : 0 ≤ target := by linarith
  have hsR : (s : ℝ) ≤ 4 := by exact_mod_cast hs
  have hx := mul_le_mul_of_nonneg_right hxi htarget0
  have habs := abs_le.mp herr
  constructor <;> linarith

theorem proper_pair_error_regularization_margin
    (actual target xi : ℝ) (htarget : 1536 ≤ target) (hxi : xi ≤ 1 / 768)
    (herr : |actual - target| ≤ xi * target + 2) :
    |target - actual| ≤ target / (12 * (2 : ℝ) ^ 5) := by
  have htarget0 : 0 ≤ target := by linarith
  have hx := mul_le_mul_of_nonneg_right hxi htarget0
  rw [abs_sub_comm]
  norm_num
  linarith

end Erdos207
