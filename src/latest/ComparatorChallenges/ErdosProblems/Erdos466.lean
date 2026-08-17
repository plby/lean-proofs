import Mathlib

open Filter Metric Set
open scoped ENNReal NNReal Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Erdos466

abbrev Plane := EuclideanSpace ℝ (Fin 2)

end Erdos466

namespace Erdos466

def distToInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

end Erdos466

namespace Erdos466

def Realizable (X δ : ℝ) (n : ℕ) : Prop :=
  ∃ (c : Plane) (P : Fin n → Plane), Function.Injective P ∧
    (∀ i, P i ∈ closedBall c X) ∧
    ∀ i j, i ≠ j → δ ≤ distToInt (dist (P i) (P j))

end Erdos466

namespace Erdos466

def admissibleSizes (X δ : ℝ) : Set ℕ := {n | Realizable X δ n}

end Erdos466

namespace Erdos466

def N (X δ : ℝ) : ℕ := sSup (admissibleSizes X δ)

end Erdos466

namespace Erdos466

theorem erdos466 :
    ∃ δ : ℝ, 0 < δ ∧ Tendsto (fun X : ℝ ↦ N X δ) atTop atTop := by
  sorry

end Erdos466

end
