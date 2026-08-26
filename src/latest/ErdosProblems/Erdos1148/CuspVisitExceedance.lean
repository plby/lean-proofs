import ErdosProblems.Erdos1148.ModularHighCuspVisits
import Mathlib.MeasureTheory.Measure.Real

/-! # Visit-count exceedance events without an initial-height restriction -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

def modularCuspVisitExceedance (H : ℝ) (n : ℕ) (A : ℝ) : Set ModularOrbitSpace :=
  {x | A ≤ ((modularCuspVisitTimes H n x).card : ℝ)}

theorem cusp_visit_exceedance_mass_le (μ : Measure ModularOrbitSpace) [IsFiniteMeasure μ]
    (H Y : ℝ) (n : ℕ) (A : ℝ) :
    μ.real (modularCuspVisitExceedance H n A) ≤ μ.real (modularCusp Y) +
      μ.real (modularHighCuspVisits H Y n A) := by
  have hsub : modularCuspVisitExceedance H n A ⊆ modularCusp Y ∪ modularHighCuspVisits H Y n A := by
    intro x hx
    by_cases hy : x ∈ modularCusp Y
    · exact Or.inl hy
    · exact Or.inr ⟨hy, hx⟩
  exact (measureReal_mono hsub).trans (measureReal_union_le _ _)

end Erdos1148.DukeArithmetic
