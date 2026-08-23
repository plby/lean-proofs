/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators ENNReal
open Polynomial MeasureTheory Set Metric Complex

noncomputable section


namespace Erdos116

open scoped Classical in
def lemniscateProduct {n : ℕ} (a : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∏ i, (z - a i)

end Erdos116

namespace Erdos116

open scoped Classical in
theorem erdos_116 {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) :
    ENNReal.ofReal (Real.pi / (2 ^ 31 * (n : ℝ) ^ 14)) <
      volume {z : ℂ | ‖lemniscateProduct a z‖ < 1} := by
  sorry

end Erdos116

end
