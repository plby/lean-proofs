/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib


namespace Erdos537

open scoped Classical in
theorem erdos_537 : ¬(∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∀ A, A ⊆ Finset.range (N + 1) → (A.card : ℝ) ≥ ε * N
  →
  ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ a₃ ∈ A, ∃ p₁ p₂ p₃, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
  p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧ a₁ * p₁ = a₂ * p₂ ∧ a₂ * p₂ = a₃ * p₃) := by
  sorry

end Erdos537
