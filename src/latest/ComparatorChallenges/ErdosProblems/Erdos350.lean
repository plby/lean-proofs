import Mathlib

namespace Erdos350

open scoped Real
open scoped Nat

open Finset

def DecidableDistinctSubsetSums {M : Type*} [AddCommMonoid M] [DecidableEq M]
    (A : Finset M) : Prop :=
  ∀ X ⊆ A, ∀ Y ⊆ A, X ≠ Y → X.sum id ≠ Y.sum id
end Erdos350

attribute [local instance] Classical.propDecidable


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Finset

namespace Erdos350

theorem erdos_350 (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) :
    ∑ n ∈ A, (1 / n : ℝ) < 2 := by
  sorry

end Erdos350
