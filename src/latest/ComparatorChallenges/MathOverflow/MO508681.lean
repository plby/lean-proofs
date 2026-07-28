import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace MO508681

noncomputable def r : ℝ := Real.sqrt 2 - 1

noncomputable def c : ℝ := 2 * r - 1

noncomputable def w (x : ℝ) : ℝ :=
  if x < r then c else 2 * x - 1

noncomputable def game_value : ℝ :=
  ∫ x in 0..1, w x

theorem game_value_eq : game_value = 3 - 2 * Real.sqrt 2 := by
  sorry

end MO508681
