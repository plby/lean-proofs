/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open MeasureTheory Polynomial

namespace Erdos1043

def levelSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ ≤ 1}
variable (u : ℂ)

noncomputable local instance instMeasureSpaceRealSpan (u : ℂ) : MeasureSpace ↥(ℝ ∙ u) :=
  measureSpaceOfInnerProductSpace

attribute [local instance] instMeasureSpaceRealSpan

theorem not_erdos_1043 :
    ¬ (∀ (f : ℂ[X]), f.Monic → f.degree ≥ 1 →
      ∃ (u : ℂ), ‖u‖ = 1 ∧
      volume ((ℝ ∙ u).orthogonalProjectionOnto '' levelSet f) ≤ 2) := by
  sorry

end Erdos1043
