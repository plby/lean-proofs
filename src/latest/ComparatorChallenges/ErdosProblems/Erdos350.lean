/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos350

def DecidableDistinctSubsetSums {M : Type*} [AddCommMonoid M] [DecidableEq M]
    (A : Finset M) : Prop :=
  ∀ X ⊆ A, ∀ Y ⊆ A, X ≠ Y → X.sum id ≠ Y.sum id

theorem erdos_350 (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) :
    ∑ n ∈ A, (1 / n : ℝ) < 2 := by
  sorry

end Erdos350
