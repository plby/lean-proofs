/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos532

theorem erdos_532 (c : ℕ → Fin 2) :
    ∃ A : Set ℕ, A.Infinite ∧
      ∃ color : Fin 2,
        ∀ S : Finset ℕ, S.Nonempty → ↑S ⊆ A →
          c (∑ n ∈ S, n) = color := by
  sorry

end Erdos532
