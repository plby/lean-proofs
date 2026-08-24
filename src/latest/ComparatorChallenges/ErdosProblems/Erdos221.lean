/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos221

theorem erdos_221 : ∃ A : Set ℕ,
  (∃ c > 0, ∃ x₀, ∀ x ≥ x₀, Set.ncard {a ∈ A | a ≤ x} ≤ c * x / Real.log x) ∧
  (∃ N₀, ∀ N ≥ N₀, ∃ k a, k ≥ 1 ∧ a ∈ A ∧ N = 2^k + a) := by
  sorry

end Erdos221
