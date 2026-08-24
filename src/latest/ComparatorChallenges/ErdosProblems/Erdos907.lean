/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos907

def IsAdditiveFn (H : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, H (x + y) = H x + H y

theorem erdos_907 (f : ℝ → ℝ)
    (hf : ∀ h : ℝ, 0 < h → Continuous fun x => f (x + h) - f x) :
    ∃ g H : ℝ → ℝ, Continuous g ∧ IsAdditiveFn H ∧ ∀ x, f x = g x + H x := by
  sorry

end Erdos907
