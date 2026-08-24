/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter MeasureTheory Set ProbabilityTheory
open scoped Topology

namespace Erdos523

abbrev Sample := ℕ → ℝ

noncomputable def rademacherMeasure : Measure ℝ :=
  bernoulliMeasure (1 : ℝ) (-1 : ℝ) ⟨(1 / 2 : ℝ), by norm_num⟩

noncomputable def signMeasure : Measure Sample :=
  Measure.infinitePi fun _ : ℕ ↦ rademacherMeasure

def randomPolynomial (ω : Sample) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (ω k : ℂ) * z ^ k

noncomputable def maximumModulus (ω : Sample) (n : ℕ) : ℝ :=
  sSup (range fun z : Circle ↦ ‖randomPolynomial ω n (z : ℂ)‖)

theorem erdos_523 :
    ∀ᵐ ω ∂signMeasure,
      Tendsto
        (fun n : ℕ ↦ maximumModulus ω n / Real.sqrt ((n : ℝ) * Real.log n))
        atTop (𝓝 1) := by
  sorry

end Erdos523
