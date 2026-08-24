/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos316

theorem not_erdos_316 : ¬ ∀ A : Finset ℕ, 0 ∉ A → 1 ∉ A →
    ∑ n ∈ A, (1 / n : ℚ) < 2 → ∃ (A₁ A₂ : Finset ℕ),
      Disjoint A₁ A₂ ∧ A = A₁ ∪ A₂ ∧
      ∑ n ∈ A₁, (1 / n : ℚ) < 1 ∧ ∑ n ∈ A₂, (1 / n : ℚ) <  1 := by
  sorry

end Erdos316
