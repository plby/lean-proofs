/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.WeightedUniformHypergraph

/-! # An explicit order threshold for the normalization-loss budget -/

namespace Erdos207

open scoped NNReal

theorem regularization_binomial_budget_nat
    (n r : ℕ) (hn : 0 < n) (hr : 1 ≤ r) (hsize : 16 * 2 ^ r * r ≤ n) :
    16 * 2 ^ r * Nat.choose (n - 1) (r - 1) ≤ Nat.choose n r := by
  have hid : n * Nat.choose (n - 1) (r - 1) = Nat.choose n r * r := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega), Nat.sub_add_cancel hr] using
      Nat.add_one_mul_choose_eq (n - 1) (r - 1)
  apply (mul_le_mul_iff_right₀ hn).mp
  calc
    n * (16 * 2 ^ r * Nat.choose (n - 1) (r - 1)) =
        16 * 2 ^ r * (n * Nat.choose (n - 1) (r - 1)) := by ring
    _ = 16 * 2 ^ r * (Nat.choose n r * r) := by rw [hid]
    _ = (16 * 2 ^ r * r) * Nat.choose n r := by ring
    _ ≤ n * Nat.choose n r := Nat.mul_le_mul_right _ hsize

theorem regularization_binomial_budget
    (n r : ℕ) (hn : 0 < n) (hr : 1 ≤ r) (hsize : 16 * 2 ^ r * r ≤ n) :
    (2 : ℝ≥0) ^ r * Nat.choose (n - 1) (r - 1) ≤ (1 / 16 : ℝ≥0) * Nat.choose n r := by
  have h : (16 : ℝ≥0) * 2 ^ r * Nat.choose (n - 1) (r - 1) ≤ Nat.choose n r := by
    exact_mod_cast regularization_binomial_budget_nat n r hn hr hsize
  apply (mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ≥0) < 16)).mp
  calc
    _ ≤ (Nat.choose n r : ℝ≥0) := by simpa only [mul_assoc] using h
    _ = _ := by ring

end Erdos207
