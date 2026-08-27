/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # Explicit finite-sum and denominator error estimates for greedy drift -/

namespace Erdos207

open Finset

theorem abs_sum_sub_card_mul_le_sum_error
    {I : Type*} (s : Finset I) (f e : I → ℝ) (a : ℝ)
    (h : ∀ i ∈ s, |f i - a| ≤ e i) :
    |(∑ i ∈ s, f i) - s.card * a| ≤ ∑ i ∈ s, e i := by
  calc
    |(∑ i ∈ s, f i) - s.card * a| = |∑ i ∈ s, (f i - a)| := by
      simp [sum_sub_distrib]
    _ ≤ ∑ i ∈ s, |f i - a| := abs_sum_le_sum_abs _ _
    _ ≤ _ := sum_le_sum h

theorem abs_difference_error_le
    {x y a b ex ey : ℝ} (hx : |x - a| ≤ ex) (hy : |y - b| ≤ ey) :
    |(x - y) - (a - b)| ≤ ex + ey := by
  calc
    |(x - y) - (a - b)| = |(x - a) - (y - b)| := by congr 1; ring
    _ ≤ |x - a| + |y - b| := abs_sub _ _
    _ ≤ _ := add_le_add hx hy

theorem abs_div_sub_div_le_of_errors
    {x y r A ex er : ℝ} (hr : 0 < r) (hA : 0 < A)
    (hx : |x - y| ≤ ex) (hdenom : |r - A| ≤ er) :
    |x / r - y / A| ≤ ex / r + |y| * er / (r * A) := by
  have heq : x / r - y / A = (x - y) / r + y * (A - r) / (r * A) := by
    field_simp
    ring
  rw [heq]
  calc
    |(x - y) / r + y * (A - r) / (r * A)| ≤
        |(x - y) / r| + |y * (A - r) / (r * A)| := abs_add_le _ _
    _ = |x - y| / r + |y| * |r - A| / (r * A) := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hr,
        abs_of_pos (mul_pos hr hA), abs_sub_comm A r]
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hx hr.le)
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdenom (abs_nonneg y)) (mul_pos hr hA).le)

end Erdos207
