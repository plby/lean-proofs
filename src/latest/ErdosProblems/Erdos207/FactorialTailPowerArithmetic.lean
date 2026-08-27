/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.JointInclusionFactorialTail
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Power cancellation for the first residual-degree moment

With outer stopping scale `t²`, the seventh power of the survival factor is
bounded by `(6/t²)⁴`.  The binomial ratio costs only seven powers of `t` for
each block of seven witness edges, so one inverse power remains per block.
-/

namespace Erdos207

open scoped NNReal

lemma factorial_survival_power_cancel
    (t A survival : ℝ≥0) (r : ℕ) (ht : 0 < t)
    (hsurvival : survival ^ 7 ≤ (6 / t ^ 2) ^ 4) :
    (A * t) ^ (7 * r) * survival ^ (7 * r) ≤
      (A ^ 7 * 6 ^ 4 / t) ^ r := by
  calc
    (A * t) ^ (7 * r) * survival ^ (7 * r) =
        ((A * t) ^ 7 * survival ^ 7) ^ r := by
      simp only [mul_pow, pow_mul]
    _ ≤ ((A * t) ^ 7 * (6 / t ^ 2) ^ 4) ^ r := by
      gcongr
    _ = (A ^ 7 * 6 ^ 4 / t) ^ r := by
      congr 1
      field_simp

/-- The two errors are kept separate: the survival term gains `t⁻ʳ`,
while the process-failure error pays the fixed witness-order factor. -/
lemma factorial_tail_power_bound
    (n t A ratio survival b : ℝ≥0) (r : ℕ) (ht : 0 < t)
    (hratio : ratio ≤ A * t)
    (hsurvival : survival ^ 7 ≤ (6 / t ^ 2) ^ 4) :
    n * ratio ^ (7 * r) * (survival ^ (7 * r) + b) ≤
      n * (A ^ 7 * 6 ^ 4 / t) ^ r + n * (A * t) ^ (7 * r) * b := by
  rw [mul_add]
  apply add_le_add
  · rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ zero_le
    calc
      ratio ^ (7 * r) * survival ^ (7 * r) ≤
          (A * t) ^ (7 * r) * survival ^ (7 * r) := by gcongr
      _ ≤ (A ^ 7 * 6 ^ 4 / t) ^ r :=
        factorial_survival_power_cancel t A survival r ht hsurvival
  · gcongr

end Erdos207
