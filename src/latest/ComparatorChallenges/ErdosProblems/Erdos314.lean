/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos314

noncomputable def harmonicPartialSum (n m : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc n m, (↑ℓ : ℝ)⁻¹

theorem erdos_314 (c : ℝ) (hc : c > 0) :
    ∀ N : ℕ, ∃ m n : ℕ, N ≤ n ∧
      1 ≤ harmonicPartialSum n m ∧ harmonicPartialSum n m ≤ 1 + c / (↑n) ^ 2 := by
  sorry

end Erdos314
