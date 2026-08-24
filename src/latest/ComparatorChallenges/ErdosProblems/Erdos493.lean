/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos493

theorem erdos_493 :
  ∃ k : ℕ, ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
    ∃ a : Fin k → ℤ,
      (∀ i : Fin k, (2 : ℤ) ≤ a i) ∧
      (∏ i : Fin k, a i) - (∑ i : Fin k, a i) = n := by
  sorry

end Erdos493
