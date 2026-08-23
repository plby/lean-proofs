/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos221

open scoped Classical in
theorem thm_main : ∃ A : Set ℕ,
  (∃ c > 0, ∃ x₀, ∀ x ≥ x₀, Set.ncard {a ∈ A | a ≤ x} ≤ c * x / Real.log x) ∧
  (∃ N₀, ∀ N ≥ N₀, ∃ k a, k ≥ 1 ∧ a ∈ A ∧ N = 2^k + a) := by
  sorry

end Erdos221
