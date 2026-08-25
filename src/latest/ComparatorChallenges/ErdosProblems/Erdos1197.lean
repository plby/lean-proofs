/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open MeasureTheory Set

namespace Erdos1197

def I_inf : Set ℝ := Icc (16/25 : ℝ) (2/3)

theorem not_erdos_1197 :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Ioi 0 ∧ 0 < volume E ∧
      ∀ x ∈ I_inf,
        {n : ℕ | 0 < n ∧ ∀ r : ℕ, 0 < r →
          ¬∃ e ∈ E, x = ((r : ℝ) / (n : ℝ)) * e}.Infinite := by
  sorry

end Erdos1197
