/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 372

Let `P n` be the largest prime factor of `n`, with `P 1 = 1`.  We prove that
there are infinitely many `n` for which

`P n > P (n + 1) > P (n + 2)`.

-/

namespace Erdos372

/-- The largest prime factor of `n`, or `1` when `n` has no prime factors. -/
def P (n : ℕ) : ℕ := n.primeFactors.max.getD 1

theorem erdos_372 :
    Set.Infinite
      {n : ℕ | P n > P (n + 1) ∧ P (n + 1) > P (n + 2)} := by
  sorry

end Erdos372
