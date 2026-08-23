/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos2

noncomputable section

def IsDistinctCoveringSystem (D : Finset ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ d ∈ D, 2 ≤ d) ∧ ∀ z : ℤ, ∃ d ∈ D, z ≡ a d [ZMOD d]

def HasUniformMinimumBound : Prop :=
  ∃ M : ℕ, ∀ (D : Finset ℕ) (a : ℕ → ℤ),
    IsDistinctCoveringSystem D a → ∃ d ∈ D, d < M

theorem uniformMinimumBound : HasUniformMinimumBound := by
  sorry

end

end Erdos2
