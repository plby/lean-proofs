/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1043

open MeasureTheory
open Polynomial

def levelSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ ≤ 1}
variable (u : ℂ)

noncomputable local instance instMeasureSpaceRealSpan (u : ℂ) : MeasureSpace ↥(ℝ ∙ u) :=
  measureSpaceOfInnerProductSpace
end Erdos1043

open MeasureTheory
open Polynomial

namespace Erdos1043

attribute [local instance] instMeasureSpaceRealSpan

open scoped Classical in
theorem erdos_1043 :
    ¬ (∀ (f : ℂ[X]), f.Monic → f.degree ≥ 1 →
      ∃ (u : ℂ), ‖u‖ = 1 ∧
      volume ((ℝ ∙ u).orthogonalProjectionOnto '' levelSet f) ≤ 2) := by
  sorry

end Erdos1043
