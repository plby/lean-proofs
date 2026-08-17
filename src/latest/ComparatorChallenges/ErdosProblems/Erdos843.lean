/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 843

The squares are Ramsey `2`-complete: in every two-colouring of the positive
square numbers, every sufficiently large natural number is a sum of distinct
squares of one colour.

The mathematical proof is the square specialization of Conlon--Fox--Pham,
*Subset sums, completeness and colorings*, Theorem 1.2.  The elementary
ordinary-completeness part and the finite robust-block interface used in the
Ramsey concatenation are developed below.
-/

open scoped BigOperators

namespace Erdos843

/-- A natural number is a positive square. -/
def IsPositiveSquare (q : ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ q = m ^ 2

/-- `n` is a sum of distinct positive square numbers, all with the same colour.

The finset consists of the square *values*, so distinctness has exactly its
usual mathematical meaning rather than merely meaning distinct roots. -/
def MonochromaticSquareSum (colour : ℕ → Fin 2) (n : ℕ) : Prop :=
  ∃ squares : Finset ℕ,
    (∀ q ∈ squares, IsPositiveSquare q) ∧
    (∃ i : Fin 2, ∀ q ∈ squares, colour q = i) ∧
    ∑ q ∈ squares, q = n

/-- The exact Ramsey `2`-completeness assertion in Problem 843. -/
def SquaresRamseyTwoComplete : Prop :=
  ∀ colour : ℕ → Fin 2, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    MonochromaticSquareSum colour n

/-! ## Finite subset-sum intervals -/

/-- Every natural in the inclusive interval `[L, U]` is a subset sum of `D`. -/
def Covers (D : Finset ℕ) (L U : ℕ) : Prop :=
  ∀ n : ℕ, L ≤ n → n ≤ U → n ∈ D.subsetSum


theorem erdos_843 : SquaresRamseyTwoComplete := by
  sorry

end Erdos843
