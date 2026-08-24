/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos264

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

end Erdos264
