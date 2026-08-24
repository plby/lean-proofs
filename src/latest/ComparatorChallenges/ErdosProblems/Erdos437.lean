/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos437

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

theorem erdos_437 :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      ∃ a : List ℕ, IsAdmissible x a ∧
        (x : ℝ) ^ (1 - ε) < squarePartialProductCount a := by
  sorry

end Erdos437
