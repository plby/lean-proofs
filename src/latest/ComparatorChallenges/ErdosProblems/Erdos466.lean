/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Metric

namespace Erdos466

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def distToInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

def Realizable (X δ : ℝ) (n : ℕ) : Prop :=
  ∃ (c : Plane) (P : Fin n → Plane), Function.Injective P ∧
    (∀ i, P i ∈ closedBall c X) ∧
    ∀ i j, i ≠ j → δ ≤ distToInt (dist (P i) (P j))

def admissibleSizes (X δ : ℝ) : Set ℕ := {n | Realizable X δ n}

noncomputable def N (X δ : ℝ) : ℕ := sSup (admissibleSizes X δ)

theorem erdos_466 :
    ∃ δ : ℝ, 0 < δ ∧ Tendsto (fun X : ℝ ↦ N X δ) atTop atTop := by
  sorry

end Erdos466
