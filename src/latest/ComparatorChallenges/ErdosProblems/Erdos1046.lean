/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Polynomial

/-!
# Erdős Problem 1046

The connected open lemniscate of a monic complex
polynomial is contained in a disk of radius `2`.
-/

namespace Erdos1046

/-- The open unit lemniscate of a complex polynomial. -/
def lemniscate (f : ℂ[X]) : Set ℂ := {z | ‖f.eval z‖ < 1}

theorem erdos_1046 (f : ℂ[X]) (hf : f.Monic)
    (hE : IsConnected (lemniscate f)) :
    ∃ c : ℂ, lemniscate f ⊆ Metric.ball c 2 := by
  sorry

end Erdos1046
