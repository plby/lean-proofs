/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped ArithmeticFunction.sigma

/-!
# Erdős Problem 825

Benkoski and Erdős asked whether sufficiently large abundancy forces an
integer to be a sum of distinct proper divisors.
-/

namespace Erdos825

theorem erdos_825 :
    ∃ (C : ℝ) (_ : C > 0),
      ∀ (n) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id := by
  sorry
