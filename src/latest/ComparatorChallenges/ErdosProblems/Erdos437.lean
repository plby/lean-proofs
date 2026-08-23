/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos437

open Filter
open scoped BigOperators Nat Real symmDiff

set_option autoImplicit false

/-- The product of the terms of `A` not exceeding `a`; when `A` is listed in
increasing order, this is the partial product ending at `a`. -/
def prefixProd (A : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ b ∈ A.filter (· ≤ a), b

/-- The number of square partial products in the canonical increasing listing
of a finite set of positive integers. -/
def squarePrefixCount (A : Finset ℕ) : ℕ :=
  (A.filter fun a ↦ IsSquare (prefixProd A a)).card

/-- Indices of square partial products of a list. -/
def squarePrefixIndices (a : List ℕ) : Finset ℕ :=
  (Finset.range a.length).filter fun i ↦ IsSquare ((a.take (i + 1)).prod)

/-- Number of square partial products of a list. -/
def squarePartialProductCount (a : List ℕ) : ℕ :=
  (squarePrefixIndices a).card

/-- A finite set is an admissible sequence for cutoff `x` when all its terms
lie in the interval `[1,x]`.  Its canonical increasing listing is then the
sequence in the original problem. -/
def IsAdmissible (x : ℕ) (a : List ℕ) : Prop :=
  a.Pairwise (· < ·) ∧ ∀ n ∈ a, 1 ≤ n ∧ n ≤ x

/-- The exact positive-answer statement in Erdős Problem 437. -/
def PositiveAnswer : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
    ∃ a : List ℕ, IsAdmissible x a ∧
      (x : ℝ) ^ (1 - ε) < squarePartialProductCount a

/-! ## Squares and factorization parity -/

/-- A positive natural number whose prime valuations are all even is a square. -/


theorem erdos437 : PositiveAnswer := by
  sorry

end Erdos437
