import Mathlib

namespace Erdos1048b

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

noncomputable def my_r : ℝ := 2 ^ (1/10 : ℝ)
noncomputable def my_f : Polynomial ℂ := Polynomial.X ^ 10 - Polynomial.C 2
noncomputable def my_S : Set ℂ := {z | ‖my_f.eval z‖ < 1}
end Erdos1048b

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos1048b

theorem components_small_final :
  ∀ z ∈ my_S, Metric.ediam (connectedComponentIn my_S z) < ENNReal.ofReal (2 - my_r) := by
  sorry

end Erdos1048b
