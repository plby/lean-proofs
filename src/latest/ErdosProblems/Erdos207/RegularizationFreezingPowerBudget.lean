/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationInputFailurePower

/-! # Quantitative failure budgets after fixing an independent source envelope -/

namespace Erdos207

open Filter
open scoped Topology

theorem regularization_freezing_ratio (t : ℕ) (d : ℕ) :
    (2 * (t : ℝ) ^ d * Real.exp (-(t : ℝ))) / Real.exp (-(t : ℝ) / 2) =
      2 * (t : ℝ) ^ d * Real.exp (-(t : ℝ) / 2) := by
  rw [mul_div_assoc, ← Real.exp_sub]
  congr 2
  ring

theorem eventually_regularization_freezing_budget (j R : ℕ) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ((j + 3 : ℕ) : ℝ) * 2 ^ (3 * j + 6) * (t : ℝ) ^ (R * (3 * j + 6)) * (1 / 2 : ℝ) ^ t +
        (2 * (t : ℝ) ^ (R * j) * Real.exp (-(t : ℝ))) / Real.exp (-(t : ℝ) / 2) < 1 := by
  have hfirst := polynomial_exp_neg_mul_tendsToZero 2 (1 / 2) (R * j) (by norm_num)
  have hsecond := (tendsto_pow_const_mul_const_pow_of_lt_one (R * (3 * j + 6))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
    (((j + 3 : ℕ) : ℝ) * 2 ^ (3 * j + 6))
  have hlim : Tendsto (fun t : ℕ ↦
      ((j + 3 : ℕ) : ℝ) * 2 ^ (3 * j + 6) * (t : ℝ) ^ (R * (3 * j + 6)) * (1 / 2 : ℝ) ^ t +
        2 * (t : ℝ) ^ (R * j) * Real.exp (-(t : ℝ) / 2)) atTop (𝓝 0) := by
    convert hsecond.add hfirst using 1 <;> simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨max T 1, le_max_right _ _, fun t ht ↦ ?_⟩
  rw [regularization_freezing_ratio]
  exact hT t ((le_max_left _ _).trans ht)

theorem regularization_frozen_failure_tendsToZero :
    Tendsto (fun t : ℕ ↦ Real.exp (-(t : ℝ) / 2)) atTop (𝓝 0) := by
  convert polynomial_exp_neg_mul_tendsToZero 1 (1 / 2) 0 (by norm_num) using 1 <;>
    simp [div_eq_mul_inv, mul_comm]

end Erdos207
