import Mathlib

namespace List

end List

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

namespace Erdos226

attribute [local instance] Classical.propDecidable

def IsAffine (f : ℝ → ℝ) : Prop :=
  ∃ a b : ℝ, ∀ x, f x = a * x + b
def PreservesRationality (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, x ∈ (Set.range ((↑) : ℚ → ℝ)) ↔ f x ∈ (Set.range ((↑) : ℚ → ℝ))
end Erdos226

attribute [local instance] Classical.propDecidable

namespace Erdos226

theorem erdos_226 : ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ x : ℝ, (F x).im = 0) ∧ ¬ IsAffine (fun x : ℝ => (F x).re) ∧ PreservesRationality (fun x : ℝ => (F x).re) := by
  sorry

end Erdos226
