import Mathlib

open Polynomial Finset Pointwise

namespace Erdos485b

open scoped Classical in
theorem exists_complete_poly_with_sparse_square (n : ℕ) (hn : 0 < n) :
    ∃ f : ℤ[X],
      f.natDegree = n ∧
      (∀ i : ℕ, i ≤ n → f.coeff i ≠ 0) ∧
      ((f ^ 2).support.card : ℝ) <
        (1 / 5 : ℝ) * (102 * (n : ℝ) ^ (Real.log 6 / Real.log 9) - 12) := by
  sorry

end Erdos485b

namespace Erdos485b

open scoped Classical in
theorem exists_complete_poly_with_sparse_square_improved (n : ℕ) (hn : 0 < n) :
    ∃ f : ℝ[X],
      f.natDegree = n ∧
      (∀ i : ℕ, i ≤ n → f.coeff i ≠ 0) ∧
      ((f ^ 2).support.card : ℝ) <
        (1 / 7 : ℝ) * (170 * (n : ℝ) ^ (Real.log 8 / Real.log 13) - 14) := by
  sorry

end Erdos485b
