/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos2

def IsDistinctCoveringSystem (D : Finset ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ d ∈ D, 2 ≤ d) ∧ ∀ z : ℤ, ∃ d ∈ D, z ≡ a d [ZMOD d]

theorem erdos_2 :
    ∃ M : ℕ, ∀ (D : Finset ℕ) (a : ℕ → ℤ),
      IsDistinctCoveringSystem D a → ∃ d ∈ D, d < M := by
  sorry

end Erdos2
