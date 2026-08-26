/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Order.Monotone.Basic

namespace Erdos341

/-- A positive increasing sequence obeys the least pair-sum-avoiding rule
following a finite initial segment, but its consecutive gaps have no eventual
period. Equal summands are allowed in the pair sums. -/
theorem not_erdos_341 :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, 0 < a n) ∧
      (∃ k : ℕ, ∀ n : ℕ, k ≤ n →
        (¬ ∃ i ≤ n, ∃ j ≤ n, a i + a j = a (n + 1)) ∧
        ∀ t : ℕ, a n < t → t < a (n + 1) →
          ∃ i ≤ n, ∃ j ≤ n, a i + a j = t) ∧
      ¬ ∃ N p : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n →
        a (n + p + 1) - a (n + p) = a (n + 1) - a n := by
  sorry

end Erdos341
