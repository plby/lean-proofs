import Mathlib

attribute [local instance] Classical.propDecidable

open Filter Topology Set Real

namespace Erdos1125

theorem erdos_1125 {f : ℝ → ℝ}
    (hf : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) :
    Monotone f := by
  sorry

end Erdos1125
