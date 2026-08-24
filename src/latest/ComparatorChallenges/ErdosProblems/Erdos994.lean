/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos994

open scoped Classical in
/-- The normalized number of visits of the fractional parts
`fract (k * α)`, `1 ≤ k ≤ n`, to `E`.

At `n = 0` this is `0`, by the usual field convention for division by zero. -/
noncomputable def visitAverage (E : Set ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n,
      if Int.fract ((k : ℝ) * α) ∈ E then (1 : ℝ) else 0) / (n : ℝ)

/-- The visit averages for `E` and `α` converge to the Lebesgue measure of `E`. -/
def HasExpectedLimit (E : Set ℝ) (α : ℝ) : Prop :=
  Tendsto (visitAverage E α) atTop (𝓝 (volume E).toReal)

/-- A parameter `α` is simultaneously good if the expected limit holds for every
Lebesgue measurable subset of `(0, 1)`. -/
def SimultaneouslyGood (α : ℝ) : Prop :=
  ∀ E : Set ℝ, MeasurableSet E → E ⊆ Ioo (0 : ℝ) 1 → HasExpectedLimit E α

/-- The simultaneous assertion fails. -/
theorem not_erdos_994 :
    ¬(∀ᵐ α : ℝ, Erdos994.SimultaneouslyGood α) := by
  sorry

end Erdos994
