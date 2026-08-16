import Mathlib

attribute [local instance] Classical.propDecidable

namespace Erdos493

theorem erdos_493_aristotle :
  ∃ k : ℕ, ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
    ∃ a : Fin k → ℤ,
      (∀ i : Fin k, (2 : ℤ) ≤ a i) ∧
      (∏ i : Fin k, a i) - (∑ i : Fin k, a i) = n := by
  sorry

end Erdos493
