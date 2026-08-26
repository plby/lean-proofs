/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1148

theorem erdos_1148 :
    ∃ N : ℤ, ∀ n : ℤ, n ≥ N → ∃ x y z : ℤ,
      n = x ^ 2 + y ^ 2 - z ^ 2 ∧ max (x ^ 2) (max (y ^ 2) (z ^ 2)) ≤ n := by
  sorry

end Erdos1148
