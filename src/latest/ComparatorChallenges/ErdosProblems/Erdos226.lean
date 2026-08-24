/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos226

def IsAffine (f : ℝ → ℝ) : Prop :=
  ∃ a b : ℝ, ∀ x, f x = a * x + b
def PreservesRationality (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, x ∈ (Set.range ((↑) : ℚ → ℝ)) ↔ f x ∈ (Set.range ((↑) : ℚ → ℝ))

theorem erdos_226 : ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ x : ℝ, (F x).im = 0) ∧ ¬ IsAffine (fun x : ℝ => (F x).re) ∧ PreservesRationality (fun x : ℝ => (F x).re) := by
  sorry

end Erdos226
