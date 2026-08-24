/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos53

variable {M : Type*} [CommMonoid M] [DecidableEq M]

def subsetProducts (A : Finset M) : Finset M :=
  A.powerset.image fun B ↦ ∏ b ∈ B, b

def sumProdValues (A : Finset ℤ) : Finset ℤ :=
  A.subsetSum ∪ subsetProducts A

theorem erdos_53 :
    ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset ℤ,
      N ≤ A.card → A.card ^ k ≤ (sumProdValues A).card := by
  sorry

end Erdos53
