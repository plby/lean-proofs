/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped Pointwise

namespace Erdos818

theorem erdos_818
    (A : Finset ℝ) (hcard : 5 ≤ A.card)
    (c : ℕ)
    (hc : (A + A).card ≤ c * A.card) :
    A.card ^ 2 ≤
      324 * c ^ 2 * Nat.clog 2 A.card *
        (A * A).card := by
  sorry

end Erdos818
