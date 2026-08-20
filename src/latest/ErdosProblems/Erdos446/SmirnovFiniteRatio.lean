/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovNumerics

/-!
# Erdős Problem 446: the finite first-crossing ratio

The finite first-crossing proof of Ford's Smirnov comparison compares two
suffix alphabets whose cardinalities are `N + c` and `N - c`.  This file
records the elementary exponential lower bound for that ratio.
-/

namespace Erdos446

open Real

/-- The symmetric logarithmic quotient dominates its tangent at zero. -/
theorem two_mul_le_log_div_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    2 * x ≤ Real.log ((1 + x) / (1 - x)) := by
  have hp : 0 < 1 + x := by linarith
  have hm : 0 < 1 - x := by linarith
  have hy : 0 ≤ x / (1 - x) := div_nonneg hx0 hm.le
  have hplus := Real.le_log_one_add_of_nonneg hx0
  have hminus := Real.le_log_one_add_of_nonneg hy
  have hone : 1 + x / (1 - x) = 1 / (1 - x) := by
    field_simp [hm.ne']
    ring
  rw [hone] at hminus
  have hlog :
      Real.log ((1 + x) / (1 - x)) =
        Real.log (1 + x) + Real.log (1 / (1 - x)) := by
    rw [Real.log_div hp.ne' hm.ne']
    rw [show 1 / (1 - x) = (1 - x)⁻¹ by simp [one_div], Real.log_inv]
    ring
  rw [hlog]
  calc
    2 * x ≤ 2 * x / (x + 2) +
        2 * (x / (1 - x)) / (x / (1 - x) + 2) := by
      field_simp [hm.ne']
      nlinarith [sq_nonneg x]
    _ ≤ Real.log (1 + x) + Real.log (1 / (1 - x)) :=
      add_le_add hplus hminus

/-- The ratio of the two symmetric finite suffix alphabets is at least its
limiting exponential value. -/
theorem exp_two_mul_le_ratio_pow {N c : ℕ} (hcN : c < N) :
    Real.exp (2 * (c : ℝ)) ≤
      (((N + c : ℕ) : ℝ) / ((N - c : ℕ) : ℝ)) ^ N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hcN)
  let x : ℝ := (c : ℝ) / N
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x < 1 := by
    dsimp [x]
    exact (div_lt_one hN).2 (by exact_mod_cast hcN)
  have hlog := two_mul_le_log_div_one_sub hx0 hx1
  have hmul : 2 * (c : ℝ) ≤
      (N : ℝ) * Real.log ((1 + x) / (1 - x)) := by
    have h := mul_le_mul_of_nonneg_left hlog hN.le
    calc
      2 * (c : ℝ) = (N : ℝ) * (2 * x) := by
        dsimp [x]
        field_simp [hN.ne']
      _ ≤ (N : ℝ) * Real.log ((1 + x) / (1 - x)) := h
  calc
    Real.exp (2 * (c : ℝ)) ≤
        Real.exp ((N : ℝ) * Real.log ((1 + x) / (1 - x))) :=
      Real.exp_le_exp.mpr hmul
    _ = (((N + c : ℕ) : ℝ) / ((N - c : ℕ) : ℝ)) ^ N := by
      have hratio : 0 < (1 + x) / (1 - x) :=
        div_pos (by linarith) (by linarith)
      rw [Real.exp_nat_mul, Real.exp_log hratio]
      congr 1
      dsimp [x]
      push_cast [Nat.cast_sub hcN.le]
      field_simp [hN.ne']

end Erdos446
