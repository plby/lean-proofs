/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Polynomial

namespace Erdos485b

theorem erdos_485 (n : ℕ) (hn : 0 < n) :
    ∃ f : ℤ[X],
      f.natDegree = n ∧
      (∀ i : ℕ, i ≤ n → f.coeff i ≠ 0) ∧
      ((f ^ 2).support.card : ℝ) <
        (1 / 5 : ℝ) * (102 * (n : ℝ) ^ (Real.log 6 / Real.log 9) - 12) := by
  sorry

theorem erdos_485_improved (n : ℕ) (hn : 0 < n) :
    ∃ f : ℝ[X],
      f.natDegree = n ∧
      (∀ i : ℕ, i ≤ n → f.coeff i ≠ 0) ∧
      ((f ^ 2).support.card : ℝ) <
        (1 / 7 : ℝ) * (170 * (n : ℝ) ^ (Real.log 8 / Real.log 13) - 14) := by
  sorry

end Erdos485b
