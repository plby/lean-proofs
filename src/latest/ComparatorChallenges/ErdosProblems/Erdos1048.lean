/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Std.Tactic.BVDecide.LRAT.Internal.Clause

open Polynomial

theorem Erdos1048.not_erdos_1048 :
    Not (∀ f : ℂ[X],
      f.Monic →
      Polynomial.degree f ≥ 1 →
    ∀ r : ℝ,
      r < 2 →
      (∀ z : ℂ, f.IsRoot z → ‖z‖ ≤ r) →
        let U : Set ℂ := { z : ℂ | ‖f.eval z‖ < 1 }
        ∃ x : ↥U,
          (2 - r) ≤
            Metric.diam (Subtype.val '' (connectedComponent x : Set (↥U)))) := by
  sorry
