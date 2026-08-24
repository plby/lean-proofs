/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped ArithmeticFunction.sigma

/-- Erdős Problem 48: Euler's totient and the sum-of-divisors function have
infinitely many common values. -/
theorem erdos_48 :
    {p : ℕ × ℕ | p.1.totient = σ 1 p.2}.Infinite := by
  sorry
