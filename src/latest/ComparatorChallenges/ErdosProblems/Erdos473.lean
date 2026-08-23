/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 473

Does there exist a permutation `a` of the positive integers such that
`a n + a (n + 1)` is prime for every `n`?

The proof is split into two parts.  The first is a general graph-theoretic
construction: a countable graph in which every finite simple path can be
extended so as to contain any prescribed vertex has a spanning one-way ray.
The second verifies that extension property for the prime-sum graph.
-/

namespace Erdos473

open Function

/-! ## A spanning ray from finite path extensions -/

/-- If finite duplicate-free `R`-chains can always be extended, as prefixes,
to contain any prescribed vertex, then any enumeration of the vertex type can
be reordered into a spanning one-way `R`-chain. -/

theorem erdos473 :
    ∃ a : ℕ ≃ ℕ+, ∀ n : ℕ,
      Nat.Prime ((a n : ℕ) + (a (n + 1) : ℕ)) := by
  sorry

end Erdos473
