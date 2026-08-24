/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 843

The squares are Ramsey `2`-complete: in every two-colouring of the positive
square numbers, every sufficiently large natural number is a sum of distinct
squares of one colour.

-/

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

/-! ## Finite subset-sum intervals -/

theorem erdos_843 :
    ∀ colour : ℕ → Fin 2, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Erdos843.MonochromaticSquareSum colour n := by
  sorry

end Erdos843
