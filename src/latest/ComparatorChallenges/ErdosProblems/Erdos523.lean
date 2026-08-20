import Mathlib

open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory Metric Set
open ProbabilityTheory

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos523

abbrev Sample := ℕ → ℝ

end Erdos523

namespace Erdos523

def rademacherMeasure : Measure ℝ :=
  bernoulliMeasure (1 : ℝ) (-1 : ℝ) ⟨(1 / 2 : ℝ), by norm_num⟩

end Erdos523

namespace Erdos523

def signMeasure : Measure Sample :=
  Measure.infinitePi fun _ : ℕ ↦ rademacherMeasure

end Erdos523

namespace Erdos523

def randomPolynomial (ω : Sample) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (ω k : ℂ) * z ^ k

end Erdos523

namespace Erdos523

def maximumModulus (ω : Sample) (n : ℕ) : ℝ :=
  sSup (range fun z : Circle ↦ ‖randomPolynomial ω n (z : ℂ)‖)

end Erdos523

namespace Erdos523

def Erdos523Statement : Prop :=
  ∀ᵐ ω ∂signMeasure,
    Tendsto
      (fun n : ℕ ↦ maximumModulus ω n / Real.sqrt ((n : ℝ) * Real.log n))
      atTop (𝓝 1)

end Erdos523

namespace Erdos523

theorem erdos523 : Erdos523Statement := by
  sorry

end Erdos523

end
