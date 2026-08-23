/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators

namespace Erdos532

open scoped Classical in
theorem erdos532 (c : ℕ → Fin 2) :
    ∃ A : Set ℕ, A.Infinite ∧
      ∃ color : Fin 2,
        ∀ S : Finset ℕ, S.Nonempty → ↑S ⊆ A →
          c (∑ n ∈ S, n) = color := by
  sorry

end Erdos532
