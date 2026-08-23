/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Real.Irrational

open scoped ArithmeticFunction.sigma


open scoped Classical in
theorem Erdos250.erdos_250 :
    ∀ x : ℝ, HasSum (fun n : ℕ => σ 1 n / (2 : ℝ) ^ n) x → Irrational x := by
  sorry
