/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Erdos327

theorem erdos_327 :
    (∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ a + b ∣ a * b) ∧
        (1 / 2 + ε) * (N : ℝ) ≤ (A.card : ℝ)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ a + b ∣ 2 * a * b) ∧
        c * (N : ℝ) ≤ (A.card : ℝ)) :=
  by sorry

end Erdos327
