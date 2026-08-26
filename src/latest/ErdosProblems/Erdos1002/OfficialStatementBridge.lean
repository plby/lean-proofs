import ErdosProblems.Erdos1002.VerifiedMain
import ErdosProblems.Erdos1002.ProbabilityFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Official existential formulation of Erdős Problem 1002

This file packages the explicit Cauchy limit into the traditional statement:
there exists a nondecreasing distribution function with limits zero and one
whose values are the limiting distribution of the fixed-start sums.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- Erdős Problem 1002 in its existential distribution-function form.

The witness is the centered Cauchy distribution function of scale `1 / (2π)`.
-/
theorem erdos1002_official :
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
  refine ⟨cauchyLimitCDF, cauchyLimitStieltjes.mono,
    tendsto_cauchyLimitCDF_atBot, tendsto_cauchyLimitCDF_atTop, ?_⟩
  intro c
  simpa only [distributionValue, normalizedRotationSum, rotationSum, sawtooth,
    div_eq_mul_inv, mul_comm, one_mul] using! erdos1002 c

end

end Erdos1002
