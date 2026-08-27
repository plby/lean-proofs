/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Squared-error bounds that do not require the perturbed profile to be positive -/

namespace Erdos4b.FGKMT

open scoped BigOperators

theorem square_error_of_abs_error {y z V ε : ℝ} (hV : 0 ≤ V)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hz : |z| ≤ V) (hy : |y - z| ≤ ε * V) :
    |y ^ 2 - z ^ 2| ≤ 3 * ε * V ^ 2 := by
  have hsum : |y + z| ≤ 3 * V := by
    calc
      _ = |(y - z) + 2 * z| := by congr 1; ring
      _ ≤ |y - z| + |2 * z| := abs_add_le _ _
      _ = |y - z| + 2 * |z| := by rw [abs_mul]; norm_num
      _ ≤ ε * V + 2 * V := add_le_add hy (mul_le_mul_of_nonneg_left hz (by norm_num))
      _ ≤ _ := by nlinarith
  rw [show y ^ 2 - z ^ 2 = (y - z) * (y + z) by ring, abs_mul]
  calc
    _ ≤ (ε * V) * (3 * V) := mul_le_mul hy hsum (abs_nonneg _) (mul_nonneg hε hV)
    _ = _ := by ring

theorem weighted_square_error {α : Type*} [Fintype α] {A ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (y f V w : α → ℝ) (hf : ∀ r, 0 ≤ f r) (hV : ∀ r, f r ≤ V r)
    (hw : ∀ r, 0 ≤ w r) (herror : ∀ r, |y r - A * f r| ≤ ε * A * V r) :
    |(∑ r, y r ^ 2 * w r) - A ^ 2 * ∑ r, f r ^ 2 * w r| ≤
      3 * ε * A ^ 2 * ∑ r, V r ^ 2 * w r := by
  classical
  have hpoint (r : α) : |y r ^ 2 - A ^ 2 * f r ^ 2| ≤ 3 * ε * A ^ 2 * V r ^ 2 := by
    have hz : |A * f r| ≤ A * V r := by
      rw [abs_of_nonneg (mul_nonneg hA (hf r))]
      exact mul_le_mul_of_nonneg_left (hV r) hA
    have h := square_error_of_abs_error (mul_nonneg hA ((hf r).trans (hV r))) hε hε1 hz
      (by simpa only [mul_assoc] using herror r)
    simpa only [mul_pow, mul_assoc] using h
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r, |y r ^ 2 * w r - A ^ 2 * (f r ^ 2 * w r)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, (3 * ε * A ^ 2 * V r ^ 2) * w r := by
      apply Finset.sum_le_sum
      intro r _hr
      rw [← mul_assoc, ← sub_mul, abs_mul, abs_of_nonneg (hw r)]
      exact mul_le_mul_of_nonneg_right (hpoint r) (hw r)
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.weighted_square_error
