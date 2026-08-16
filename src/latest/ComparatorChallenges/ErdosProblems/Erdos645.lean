import Mathlib

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos645

theorem erdos_645 (c : ℕ → Bool) :
    ∃ x d, 0 < x ∧ x < d ∧
      (∃ C, c x = C ∧ c (x + d) = C ∧ c (x + 2 * d) = C) := by
  sorry

end Erdos645
