/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped ArithmeticFunction.sigma

namespace Erdos946

theorem erdos_946 : Set.Infinite {n : ℕ | σ 0 n = σ 0 (n + 1)} := by
  sorry

end Erdos946
