import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős Problem 1002: exact statement

The theorem is stated directly in terms of Lebesgue distribution
functions.  This keeps the fixed starting point, the full integer sequence,
every real threshold, and the normalization from the original problem
explicit.
-/

open Filter MeasureTheory Set
open scoped BigOperators

namespace Erdos1002

noncomputable section

/-- The centered sawtooth used in Erdős Problem 1002. -/
def sawtooth (x : ℝ) : ℝ :=
  (1 : ℝ) / 2 - Int.fract x

/-- The finite rotation sum from k = 1 through k = N. -/
def rotationSum (N : ℕ) (α : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, sawtooth ((k : ℝ) * α)

/-- The normalization appearing in the problem. -/
def normalizedRotationSum (N : ℕ) (α : ℝ) : ℝ :=
  rotationSum N α / Real.log (N : ℝ)

/-- The finite-N distribution function under uniform Lebesgue measure
on the open unit interval. -/
def distributionValue (N : ℕ) (c : ℝ) : ℝ :=
  (volume
    {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ normalizedRotationSum N α ≤ c}).toReal

/-- The centered Cauchy distribution function with scale 1 / (2π). -/
def cauchyLimitCDF (c : ℝ) : ℝ :=
  (1 : ℝ) / 2 + (1 / Real.pi) * Real.arctan (2 * Real.pi * c)

/-- The exact affirmative conclusion of Erdős Problem 1002 claimed by
the manuscript. -/
def Erdos1002Conclusion : Prop :=
  ∀ c : ℝ,
    Tendsto (fun N : ℕ => distributionValue N c) atTop
      (nhds (cauchyLimitCDF c))

end

end Erdos1002
