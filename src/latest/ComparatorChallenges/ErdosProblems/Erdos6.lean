/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace BoundedGaps

noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

end BoundedGaps

/-!
# Erdős Problem 6

The gaps between consecutive primes contain infinitely many strictly
increasing runs of length three.
-/

namespace Erdos6

open Set

/-- The gap after the zero-based `n`th prime. -/
noncomputable abbrev primeGap (n : ℕ) : ℕ := BoundedGaps.primeGap n

theorem erdos_6 :
    {n | primeGap n < primeGap (n + 1) ∧
      primeGap (n + 1) < primeGap (n + 2)}.Infinite := by
  sorry
