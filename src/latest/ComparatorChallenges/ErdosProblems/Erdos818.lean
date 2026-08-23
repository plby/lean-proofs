/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped Pointwise


open Finset
open scoped Pointwise BigOperators

namespace Erdos818

open scoped Classical in
theorem erdos_problem_818_general
    (A : Finset ℝ) (hcard : 5 ≤ A.card)
    (c : ℕ)
    (hc : (A + A).card ≤ c * A.card) :
    A.card ^ 2 ≤
      324 * c ^ 2 * Nat.clog 2 A.card *
        (A * A).card := by
  sorry

end Erdos818
