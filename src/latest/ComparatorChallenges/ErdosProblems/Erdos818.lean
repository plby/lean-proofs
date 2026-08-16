import Mathlib

open scoped Pointwise

attribute [local instance] Classical.propDecidable

open Finset
open scoped Pointwise BigOperators

namespace Erdos818

theorem erdos_problem_818_general
    (A : Finset ℝ) (hcard : 5 ≤ A.card)
    (c : ℕ)
    (hc : (A + A).card ≤ c * A.card) :
    A.card ^ 2 ≤
      324 * c ^ 2 * Nat.clog 2 A.card *
        (A * A).card := by
  sorry

end Erdos818
