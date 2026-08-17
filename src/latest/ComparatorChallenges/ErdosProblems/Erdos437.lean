/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of the positive resolution of Erdős Problem 437.
https://www.erdosproblems.com/437

For every ε > 0 and every sufficiently large x, we construct a strictly
increasing finite sequence in [1,x] with more than x^(1-ε) square partial
products.  The finite combinatorial core is Lemma 4.2 of Bui--Pratt--
Zaharescu; the reservoir used here consists of fixed-size products of small
primes, so the only analytic input required for the qualitative result is the
prime number theorem.

Mathematical sources:
- H. M. Bui, K. Pratt, A. Zaharescu, Math. Proc. Camb. Phil. Soc. 176 (2024).
- T. Tao, "A result of Bui--Pratt--Zaharescu, and Erdős problem #437" (2024).

A detailed mathematical proof, including Tao's sharper quantitative bounds,
is in `tex/437.tex`.
-/

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
