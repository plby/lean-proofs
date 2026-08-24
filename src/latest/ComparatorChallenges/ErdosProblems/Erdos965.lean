/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 965

There is a two-coloring of `ℝ` for which every uncountable set has two distinct
pair sums of different colors.  Thus the answer is negative.
-/

namespace Erdos965

theorem not_erdos_965 :
    ¬ ∀ f : ℝ → Fin 2, ∃ A : Set ℝ, ¬ A.Countable ∧
      ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A), a ≠ b → c ≠ d →
        f (a + b) = f (c + d) := by
  sorry
