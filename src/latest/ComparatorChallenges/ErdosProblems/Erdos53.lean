import Mathlib

open scoped BigOperators Pointwise
open Filter Asymptotics
open scoped BigOperators NNReal
open scoped BigOperators
open ZMod

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Erdos53

variable {M : Type*} [CommMonoid M] [DecidableEq M]

def subsetProducts (A : Finset M) : Finset M :=
  A.powerset.image fun B ↦ ∏ b ∈ B, b

end Erdos53

namespace Erdos53

def sumProdValues (A : Finset ℤ) : Finset ℤ :=
  A.subsetSum ∪ subsetProducts A

end Erdos53

namespace Erdos53

theorem erdos53 :
    ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset ℤ,
      N ≤ A.card → A.card ^ k ≤ (sumProdValues A).card := by
  sorry

end Erdos53

end
