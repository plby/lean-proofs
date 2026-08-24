/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos651

def HasSubexponentialUpperBound (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in Filter.atTop,
      (f n : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ))

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

def InGeneralPosition (d : ℕ) (X : Finset (Point d)) : Prop :=
  ∀ S : Finset (Point d), S ⊆ X → S.card = d + 1 →
    AffineIndependent ℝ (fun p : ↥S ↦ (p : Point d))

def InConvexPosition {d : ℕ} (X : Finset (Point d)) : Prop :=
  ∀ x ∈ X, x ∉ convexHull ℝ (↑(X.erase x) : Set (Point d))

def ContainsConvexSubset (d n : ℕ) (X : Finset (Point d)) : Prop :=
  ∃ Y : Finset (Point d), Y ⊆ X ∧ Y.card = n ∧ InConvexPosition Y

def ForcesConvexSubset (d n N : ℕ) : Prop :=
  ∀ X : Finset (Point d), N ≤ X.card → InGeneralPosition d X →
    ContainsConvexSubset d n X

noncomputable def erdosSzekeresNumber (d n : ℕ) : ℕ :=
  sInf {N : ℕ | ForcesConvexSubset d n N}

def HasExponentialLowerBound (f : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in Filter.atTop, (1 + c) ^ n < (f n : ℝ)

theorem not_erdos_651 :
    ¬ ((Erdos651.HasSubexponentialUpperBound (Erdos651.erdosSzekeresNumber 3)) ∧ (Erdos651.HasExponentialLowerBound (Erdos651.erdosSzekeresNumber 3))) := by
  sorry

end Erdos651
