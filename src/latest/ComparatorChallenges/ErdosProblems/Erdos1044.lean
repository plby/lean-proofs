/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open MeasureTheory

namespace Erdos1044

def OmegaSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ < 1}

noncomputable def componentBoundaryLength (f : Polynomial ℂ) (z : ℂ) : ENNReal :=
  μH[(1 : ℝ)] (frontier (connectedComponentIn (OmegaSet f) z))

noncomputable def LambdaFn (f : Polynomial ℂ) : ENNReal :=
  ⨆ z ∈ OmegaSet f, componentBoundaryLength f z

def IsAdmissible (f : Polynomial ℂ) : Prop :=
  f.Monic ∧ ∀ z : ℂ, f.IsRoot z → ‖z‖ ≤ 1

noncomputable def lambdaInf : ENNReal :=
  ⨅ (f : Polynomial ℂ) (_ : IsAdmissible f ∧ f.natDegree ≥ 1), LambdaFn f

theorem erdos_1044 : lambdaInf = 2 := by
  sorry

end Erdos1044
