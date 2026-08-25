/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter MeasureTheory Metric

namespace Erdos232

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def UnitDistanceFree (A : Set Plane) : Prop :=
  ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → dist x y ≠ 1

noncomputable def ballDensity (A : Set Plane) (R : ℝ) : ℝ :=
  (volume (A ∩ ball 0 R)).toReal / (volume (ball (0 : Plane) R)).toReal

noncomputable def upperDensity (A : Set Plane) : ℝ :=
  limsup (ballDensity A) atTop

noncomputable def admissibleDensities : Set ℝ :=
  {d | ∃ A : Set Plane, MeasurableSet A ∧ UnitDistanceFree A ∧ upperDensity A = d}

noncomputable def m1 : ℝ :=
  sSup admissibleDensities

theorem erdos_232 :
    m1 ≤ (247 / 1000 : ℝ) := by
  sorry

end Erdos232
