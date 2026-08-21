import Mathlib

syntax (name := answerSyntax228Challenge) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

namespace Erdos228

theorem erdos_228 :
    answer(True) ↔ ∃ (c₁ : ℝ) (c₂ : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    ∃ p : Polynomial ℂ, p.degree = n ∧
    (∀ i ≤ n, p.coeff i = 1 ∨ p.coeff i = -1) ∧
    ∀ z : ℂ, ‖z‖ = 1 →
    (√n < c₁ * ‖p.eval z‖ ∧ ‖p.eval z‖ < c₂ * √n) := by
  sorry

end Erdos228
