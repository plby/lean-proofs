/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped Pointwise

namespace Erdos35

/-- The exact order-`k` additive-basis predicate used in Problem 35.  Pointwise
natural scalar multiplication is the `k`-fold sumset, with `0 • B = {0}`. -/
def IsAdditiveBasisOfOrder (B : Set ℕ) (k : ℕ) : Prop :=
  k • B = Set.univ

open scoped Classical in
theorem erdos_35 (A B : Set ℕ) (k : ℕ) (_hzero : 0 ∈ B)
    (hBasis : IsAdditiveBasisOfOrder B k) :
    schnirelmannDensity A +
        schnirelmannDensity A * (1 - schnirelmannDensity A) / k ≤
      schnirelmannDensity (A + B) := by
  sorry

end Erdos35
