/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos490

theorem erdos_490 :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ A B : Finset ℕ,
        A ⊆ Finset.Icc 1 n → B ⊆ Finset.Icc 1 n →
        (∀ a₁ ∈ A, ∀ b₁ ∈ B, ∀ a₂ ∈ A, ∀ b₂ ∈ B,
          a₁ * b₁ = a₂ * b₂ → a₁ = a₂ ∧ b₁ = b₂) →
        A.card * B.card < 60 * n ^ 2 / Real.log n := by
  sorry

end Erdos490
