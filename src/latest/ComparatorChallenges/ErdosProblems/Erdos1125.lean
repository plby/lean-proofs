/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1125

theorem erdos_1125 {f : ℝ → ℝ}
    (hf : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) :
    Monotone f := by
  sorry

end Erdos1125
