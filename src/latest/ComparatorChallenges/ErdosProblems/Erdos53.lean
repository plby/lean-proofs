/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators Pointwise
open Filter Asymptotics
open scoped BigOperators NNReal
open scoped BigOperators
open ZMod

noncomputable section


namespace Erdos53

variable {M : Type*} [CommMonoid M] [DecidableEq M]

open scoped Classical in
def subsetProducts (A : Finset M) : Finset M :=
  A.powerset.image fun B ↦ ∏ b ∈ B, b

end Erdos53

namespace Erdos53

open scoped Classical in
def sumProdValues (A : Finset ℤ) : Finset ℤ :=
  A.subsetSum ∪ subsetProducts A

end Erdos53

namespace Erdos53

open scoped Classical in
theorem erdos53 :
    ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset ℤ,
      N ≤ A.card → A.card ^ k ≤ (sumProdValues A).card := by
  sorry

end Erdos53

end
