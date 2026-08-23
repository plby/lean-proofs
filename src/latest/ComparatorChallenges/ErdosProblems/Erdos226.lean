/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace List

end List

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

namespace Erdos226


open scoped Classical in
def IsAffine (f : ℝ → ℝ) : Prop :=
  ∃ a b : ℝ, ∀ x, f x = a * x + b
open scoped Classical in
def PreservesRationality (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, x ∈ (Set.range ((↑) : ℚ → ℝ)) ↔ f x ∈ (Set.range ((↑) : ℚ → ℝ))
end Erdos226


namespace Erdos226

open scoped Classical in
theorem erdos_226 : ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ x : ℝ, (F x).im = 0) ∧ ¬ IsAffine (fun x : ℝ => (F x).re) ∧ PreservesRationality (fun x : ℝ => (F x).re) := by
  sorry

end Erdos226
