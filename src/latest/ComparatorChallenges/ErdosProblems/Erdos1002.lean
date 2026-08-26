/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

/-- The normalized rotation sums admit a distribution function, at every
real threshold and along the full sequence of natural cutoffs. -/
theorem erdos_1002 :
    ∃ g : ℝ → ℝ,
      Monotone g ∧
      Tendsto g atBot (nhds 0) ∧
      Tendsto g atTop (nhds 1) ∧
      ∀ c : ℝ,
        Tendsto
          (fun n : ℕ =>
            (volume
              {α : ℝ |
                α ∈ Ioo (0 : ℝ) 1 ∧
                  (1 / Real.log (n : ℝ)) *
                      (∑ k ∈ Finset.Icc 1 n,
                        ((1 : ℝ) / 2 - Int.fract (α * (k : ℝ)))) ≤ c}).toReal)
          atTop (nhds (g c)) := by
  sorry

/-- The limiting law is centered Cauchy with scale `1 / (2π)`. -/
theorem erdos_1002_cauchy :
    ∀ c : ℝ,
      Tendsto
        (fun N : ℕ ↦
          (volume
            {α : ℝ |
              α ∈ Ioo (0 : ℝ) 1 ∧
                (∑ k ∈ Finset.Icc 1 N,
                    ((1 : ℝ) / 2 - Int.fract ((k : ℝ) * α))) /
                    Real.log (N : ℝ) ≤ c}).toReal)
        atTop
        (nhds ((1 : ℝ) / 2 +
          (1 / Real.pi) * Real.arctan (2 * Real.pi * c))) := by
  sorry

end Erdos1002
