/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory Metric Set
open ProbabilityTheory

noncomputable section

namespace Erdos523

open scoped Classical in
abbrev Sample := ℕ → ℝ

end Erdos523

namespace Erdos523

open scoped Classical in
def rademacherMeasure : Measure ℝ :=
  bernoulliMeasure (1 : ℝ) (-1 : ℝ) ⟨(1 / 2 : ℝ), by norm_num⟩

end Erdos523

namespace Erdos523

open scoped Classical in
def signMeasure : Measure Sample :=
  Measure.infinitePi fun _ : ℕ ↦ rademacherMeasure

end Erdos523

namespace Erdos523

open scoped Classical in
def randomPolynomial (ω : Sample) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (ω k : ℂ) * z ^ k

end Erdos523

namespace Erdos523

open scoped Classical in
def maximumModulus (ω : Sample) (n : ℕ) : ℝ :=
  sSup (range fun z : Circle ↦ ‖randomPolynomial ω n (z : ℂ)‖)

end Erdos523

namespace Erdos523

open scoped Classical in
def Erdos523Statement : Prop :=
  ∀ᵐ ω ∂signMeasure,
    Tendsto
      (fun n : ℕ ↦ maximumModulus ω n / Real.sqrt ((n : ℝ) * Real.log n))
      atTop (𝓝 1)

end Erdos523

namespace Erdos523

open scoped Classical in
theorem erdos523 : Erdos523Statement := by
  sorry

end Erdos523

end
