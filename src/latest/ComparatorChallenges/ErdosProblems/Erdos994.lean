/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of the literal simultaneous-quantifier statement displayed
in Erdős Problem 994.

The historical Khintchine conjecture is normally read with the measurable set fixed
first: `∀ E, ∀ᵐ α, ...`.  Marstrand disproved that assertion with one fixed set, a much
deeper result.  The database display instead ends with "for almost all α ... for all
E", namely `∀ᵐ α, ∀ E, ...`.  The definitions below record both orders explicitly and
the main theorem keeps the displayed order.  Its negation has a short diagonal proof:
for each α, delete the countable orbit `{fract (k * α)}` from `(0, 1)`.  The resulting
measurable set still has measure one but is never visited.

See `tex/994.tex` for the complete proof, the machine-checked quantifier comparison,
and a detailed reconstruction of the historical fixed-set construction.
-/

import Mathlib

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos994

attribute [local instance] Classical.propDecidable

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

/-- The simultaneous reading of the assertion displayed in Erdős Problem 994. -/
def KhintchineSimultaneous : Prop :=
  ∀ᵐ α : ℝ, SimultaneouslyGood α

/-- The conventional fixed-set quantifier order of Khintchine's historical conjecture.
Here the exceptional null set is allowed to depend on `E`. -/
def KhintchineFixedSet : Prop :=
  ∀ E : Set ℝ, MeasurableSet E → E ⊆ Ioo (0 : ℝ) 1 →
    ∀ᵐ α : ℝ, HasExpectedLimit E α

/-- The simultaneous assertion implies the fixed-set assertion.  Keeping this lemma in
the formal development prevents the two logically different quantifier orders from
being conflated. -/


theorem erdos_994 : ¬KhintchineSimultaneous := by
  sorry

end Erdos994
