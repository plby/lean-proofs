/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Summable errors in the prime-weighted finite-field determinant estimate.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Counting

open scoped BigOperators

lemma log_div_mul_sqrt_le (x : ℝ) (hx : 0 < x) :
    Real.log x / (x * Real.sqrt x) ≤ 4 * x ^ (-(5 : ℝ) / 4) := by
  have hlog := Real.log_le_rpow_div hx.le (show (0 : ℝ) < 1 / 4 by norm_num)
  have heq : (x ^ (1 / 4 : ℝ) / (1 / 4)) / (x * Real.sqrt x) =
      4 * x ^ (-(5 : ℝ) / 4) := by
    have hden : x * Real.sqrt x = x ^ (3 / 2 : ℝ) := by
      calc
        _ = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
        _ = _ := by rw [← Real.rpow_add hx]; norm_num
    rw [hden, div_div, div_eq_mul_inv, mul_inv_rev, ← Real.rpow_neg hx.le]
    have hexp : (1 / 4 : ℝ) + -(3 / 2) = -(5 : ℝ) / 4 := by norm_num
    calc
      _ = 4 * (x ^ (1 / 4 : ℝ) * x ^ (-(3 / 2 : ℝ))) := by ring
      _ = _ := by rw [← Real.rpow_add hx, hexp]
  rw [← heq]
  exact div_le_div_of_nonneg_right hlog (mul_nonneg hx.le (Real.sqrt_nonneg x))

theorem summable_log_div_mul_sqrt :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * Real.sqrt n)) := by
  have hs : Summable (fun n : ℕ => 4 * (n : ℝ) ^ (-(5 : ℝ) / 4)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : -(5 : ℝ) / 4 < -1)).mul_left 4
  apply Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · exact div_nonneg (Real.log_natCast_nonneg n) (by positivity)
  · by_cases hn : n = 0
    · simp only [hn, Nat.cast_zero, Real.log_zero, zero_mul, zero_div]
      positivity
    · exact log_div_mul_sqrt_le n (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))

/-- A single finite constant bounds all finite logarithmic error sums. -/
theorem exists_log_sqrt_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Finset ℕ,
      (∑ n ∈ S, Real.log n / ((n : ℝ) * Real.sqrt n)) ≤ C := by
  refine ⟨∑' n : ℕ, Real.log n / ((n : ℝ) * Real.sqrt n), ?_, ?_⟩
  · exact tsum_nonneg (fun n => div_nonneg (Real.log_natCast_nonneg n) (by positivity))
  · intro S
    exact Summable.sum_le_tsum S (fun n _ =>
      div_nonneg (Real.log_natCast_nonneg n) (by positivity)) summable_log_div_mul_sqrt

#print axioms summable_log_div_mul_sqrt
-- 'Erdos477.Counting.summable_log_div_mul_sqrt' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
