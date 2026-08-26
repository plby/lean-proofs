import ErdosProblems.Erdos1148.HorocycleFixedPoints
import ErdosProblems.Erdos1148.HorocycleGeneration

/-! # Mautner's fixed-vector argument for SL(2,R) -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem specialLinear_fixed_of_diagonal_fixed {X : Type*} [MetricSpace X]
    [MulAction SL(2, ℝ) X] [ContinuousSMul SL(2, ℝ) X] [IsIsometricSMul SL(2, ℝ) X]
    {x : X} (hx : diagonalFlow 1 • x = x) (g : SL(2, ℝ)) : g • x = x := by
  obtain ⟨hs, hu⟩ := horocycles_fixed_of_diagonal_fixed hx
  exact specialLinear_fixed_of_horocycles hs hu g

end Erdos1148.DukeArithmetic
