import Mathlib

open scoped ENNReal NNReal Topology BigOperators
open Filter Metric Set

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Erdos465

abbrev Plane := ℂ

end Erdos465

namespace Erdos465

def distToInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

end Erdos465

namespace Erdos465

def Admissible (X δ : ℝ) (P : Finset Plane) : Prop :=
  (∀ p ∈ P, ‖p‖ ≤ X) ∧
    (P : Set Plane).Pairwise fun p q ↦ δ ≤ distToInt ‖p - q‖

end Erdos465

namespace Erdos465

def admissibleCardinalities (X δ : ℝ) : Set ℕ :=
  {n | ∃ P : Finset Plane, Admissible X δ P ∧ P.card = n}

end Erdos465

namespace Erdos465

def N (X δ : ℝ) : ℕ := sSup (admissibleCardinalities X δ)

end Erdos465

namespace Erdos465

theorem erdos_465 {δ : ℝ} (hδ : 0 < δ) :
    (∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
        (N X δ : ℝ) ≤ C * Real.sqrt X) ∧
      (fun X : ℝ ↦ (N X δ : ℝ)) =o[atTop] (fun X : ℝ ↦ X) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop,
        (N X δ : ℝ) < X ^ ((1 : ℝ) / 2 + ε)) := by
  sorry

end Erdos465

end
