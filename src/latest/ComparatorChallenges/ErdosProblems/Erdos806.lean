/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped Pointwise

namespace Erdos806

theorem erdos_806 :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
          (A.card : ℝ) ≤ Real.sqrt n →
          ∃ B : Finset ℤ,
            A.map (Nat.castEmbedding : ℕ ↪ ℤ) ⊆ B + B ∧
            (B.card : ℝ) ≤ ε * Real.sqrt n := by
  sorry

end Erdos806
