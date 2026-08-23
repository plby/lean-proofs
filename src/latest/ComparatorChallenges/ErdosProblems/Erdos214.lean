/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Congruence

namespace Erdos214

abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

inductive Color
  | Red
  | Blue
  deriving DecidableEq

theorem theorem_1 (c : Point → Color) (cfg : Fin 4 → Point)
    (h_blue : ∀ P Q, dist P Q = 1 → ¬(c P = Color.Blue ∧ c Q = Color.Blue)) :
    ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ i, c (cfg' i) = Color.Red := by
  sorry

theorem theorem_2 :
    ∃ (c : Point → Color) (X : Set Point),
      (∀ P Q, dist P Q = 1 → ¬(c P = Color.Blue ∧ c Q = Color.Blue)) ∧
        X.Finite ∧ X.ncard = 12 ∧
          ∀ (X' : Set Point),
            (∃ f : Point ≃ᵃⁱ[ℝ] Point, f '' X = X') → ∃ P ∈ X', c P = Color.Blue := by
  sorry

end Erdos214
