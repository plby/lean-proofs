import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Real.Irrational

open scoped ArithmeticFunction.sigma

attribute [local instance] Classical.propDecidable

theorem Erdos250.erdos_250 :
    ∀ x : ℝ, HasSum (fun n : ℕ => σ 1 n / (2 : ℝ) ^ n) x → Irrational x := by
  sorry
