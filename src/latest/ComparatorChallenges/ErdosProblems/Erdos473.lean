/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 473

Does there exist a permutation `a` of the positive integers such that
`a n + a (n + 1)` is prime for every `n`?
-/

namespace Erdos473

theorem erdos_473 :
    ∃ a : ℕ ≃ ℕ+, ∀ n : ℕ,
      Nat.Prime ((a n : ℕ) + (a (n + 1) : ℕ)) := by
  sorry

end Erdos473
