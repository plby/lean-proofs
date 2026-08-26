import Mathlib

open scoped BigOperators

/-- Every sign sequence has arbitrarily large homogeneous-progression sums. -/
theorem erdos_67 (f : ℕ → ℤ) (hf : ∀ n, f n = -1 ∨ f n = 1)
    (C : ℝ) (hC : 0 < C) :
    ∃ d m : ℕ, 1 ≤ d ∧ 1 ≤ m ∧
      C < |((∑ k ∈ Finset.Icc 1 m, f (k * d) : ℤ) : ℝ)| := by
  sorry
