import Mathlib

attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace Erdos532

theorem erdos532 (c : ℕ → Fin 2) :
    ∃ A : Set ℕ, A.Infinite ∧
      ∃ color : Fin 2,
        ∀ S : Finset ℕ, S.Nonempty → ↑S ⊆ A →
          c (∑ n ∈ S, n) = color := by
  sorry

end Erdos532
