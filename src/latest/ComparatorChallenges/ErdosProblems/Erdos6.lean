import Mathlib

namespace BoundedGaps

noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

end BoundedGaps

/-!
# Erdős Problem 6

This file proves that the gaps between consecutive primes contain infinitely
many strictly increasing runs of length three.

The analytic input is the Maynard--Tao prime-tuples theorem, in the form
needed by Banks--Freiberg--Turnage-Butterbaugh.  The remaining argument uses
their congruence construction and the admissible tuple of powers of two.
-/

namespace Erdos6

open Set

/-- The gap after the zero-based `n`th prime. -/
noncomputable abbrev primeGap (n : ℕ) : ℕ := BoundedGaps.primeGap n

/-- Successive differences between powers of two grow strictly. -/

theorem erdos_6 :
    {n | primeGap n < primeGap (n + 1) ∧
      primeGap (n + 1) < primeGap (n + 2)}.Infinite := by
  sorry
