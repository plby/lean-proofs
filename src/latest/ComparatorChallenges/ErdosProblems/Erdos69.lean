/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos69

/-- The binary series counting distinct prime factors is irrational. -/
theorem erdos_69 :
    Irrational (∑' n : ℕ,
      (ArithmeticFunction.cardDistinctFactors (n + 2) : ℝ) / 2 ^ (n + 2)) := by
  sorry

end Erdos69
