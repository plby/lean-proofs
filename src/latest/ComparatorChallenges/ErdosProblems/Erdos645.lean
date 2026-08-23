/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos645

open scoped Classical in
theorem erdos_645 (c : ℕ → Bool) :
    ∃ x d, 0 < x ∧ x < d ∧
      (∃ C, c x = C ∧ c (x + d) = C ∧ c (x + 2 * d) = C) := by
  sorry

end Erdos645
