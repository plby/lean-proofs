/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open MeasureTheory

namespace Erdos116

theorem erdos_116 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ, ∀ (n : ℕ), 0 < n → ∀ a : Fin n → ℂ,
      (∀ i, ‖a i‖ ≤ 1) →
      ENNReal.ofReal (c / (n : ℝ) ^ C) <
        volume {z : ℂ | ‖∏ i, (z - a i)‖ < 1} := by
  sorry

end Erdos116
