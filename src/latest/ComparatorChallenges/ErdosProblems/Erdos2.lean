import Mathlib

namespace Erdos2

noncomputable section

attribute [local instance] Classical.propDecidable

def IsDistinctCoveringSystem (D : Finset ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ d ∈ D, 2 ≤ d) ∧ ∀ z : ℤ, ∃ d ∈ D, z ≡ a d [ZMOD d]

def HasUniformMinimumBound : Prop :=
  ∃ M : ℕ, ∀ (D : Finset ℕ) (a : ℕ → ℤ),
    IsDistinctCoveringSystem D a → ∃ d ∈ D, d < M

theorem uniformMinimumBound : HasUniformMinimumBound := by
  sorry

end

end Erdos2
