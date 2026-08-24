/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1048b

noncomputable def my_r : ℝ := 2 ^ (1/10 : ℝ)
noncomputable def my_f : Polynomial ℂ := Polynomial.X ^ 10 - Polynomial.C 2
noncomputable def my_S : Set ℂ := {z | ‖my_f.eval z‖ < 1}

theorem erdos_1048 :
  ∀ z ∈ my_S, Metric.ediam (connectedComponentIn my_S z) < ENNReal.ofReal (2 - my_r) := by
  sorry

end Erdos1048b
