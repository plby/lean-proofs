/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos729

theorem erdos_729 (C : ℝ) (hC : C > 0) :
    ∃ K ≥ 3, Set.Infinite {T : ℕ × ℕ × ℕ |
      let a := T.1
      let b := T.2.1
      let n := T.2.2
      a > 0 ∧ b > 0 ∧ n > 0 ∧
      (a : ℝ) + b > n + C * Real.log n ∧
      ∀ p, p.Prime → p > K →
        padicValNat p ((n.factorial / (a.factorial * b.factorial) : ℚ).den) = 0} := by
  sorry

end Erdos729
