/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos402

open scoped Pointwise
open Filter Asymptotics

theorem erdos_402_of_sufficiently_large :
    ∃ N₀ : ℕ, ∀ A : Finset ℕ, N₀ ≤ A.card → 0 ∉ A → A.Nonempty →
      ∃ᵉ (a ∈ A) (b ∈ A), a.gcd b ≤ (a / A.card : ℚ) := by
  sorry
