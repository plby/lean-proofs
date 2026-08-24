/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos465

abbrev Plane := ℂ

noncomputable def distToInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

def Admissible (X δ : ℝ) (P : Finset Plane) : Prop :=
  (∀ p ∈ P, ‖p‖ ≤ X) ∧
    (P : Set Plane).Pairwise fun p q ↦ δ ≤ distToInt ‖p - q‖

def admissibleCardinalities (X δ : ℝ) : Set ℕ :=
  {n | ∃ P : Finset Plane, Admissible X δ P ∧ P.card = n}

noncomputable def N (X δ : ℝ) : ℕ := sSup (admissibleCardinalities X δ)

theorem erdos_465 {δ : ℝ} (hδ : 0 < δ) :
    (∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
        (N X δ : ℝ) ≤ C * Real.sqrt X) ∧
      (fun X : ℝ ↦ (N X δ : ℝ)) =o[atTop] (fun X : ℝ ↦ X) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop,
        (N X δ : ℝ) < X ^ ((1 : ℝ) / 2 + ε)) := by
  sorry

end Erdos465
