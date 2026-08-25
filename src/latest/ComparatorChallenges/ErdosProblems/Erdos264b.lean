/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos264b

def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  ∀ b : ℕ → ℕ,
    BddAbove (Set.range b) →
      0 ∉ Set.range (a + b) →
        0 ∉ Set.range b →
          Irrational (∑' n, (1 : ℝ) / (a n + b n))

theorem not_erdos_264 : ¬IsIrrationalitySequence (2 ^ ·) := by
  sorry

theorem erdos_264_example : IsIrrationalitySequence (fun n ↦ 2 ^ (2 ^ n)) := by
  sorry

theorem main_theorem :
    ∃ b : ℕ → ℕ, (∀ k, b k ∈ ({1, 2, 3, 4, 5} : Set ℕ)) ∧
      ∃ q : ℚ, (∑' k, 1 / ((2 : ℝ) ^ (k + 1) + (b (k + 1) : ℝ))) = (q : ℝ) := by
  sorry

end Erdos264b
