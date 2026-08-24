/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos957

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable def distanceSet (A : Finset Point) : Finset ℝ := by
  classical
  exact ((A.product A).filter fun p ↦ p.1 ≠ p.2).image fun p ↦ dist p.1 p.2

def IsMinimumDistance (A : Finset Point) (r : ℝ) : Prop :=
  r ∈ distanceSet A ∧ ∀ s ∈ distanceSet A, r ≤ s

def IsMaximumDistance (A : Finset Point) (r : ℝ) : Prop :=
  r ∈ distanceSet A ∧ ∀ s ∈ distanceSet A, s ≤ r

noncomputable def distanceGraph (A : Finset Point) (r : ℝ) :
    SimpleGraph {x // x ∈ A} where
  Adj x y := x ≠ y ∧ dist (x : Point) (y : Point) = r
  symm.symm := by
    intro x y h
    exact ⟨h.1.symm, by simpa [dist_comm] using h.2⟩
  loopless.irrefl := by
    intro x h
    exact h.1 rfl

noncomputable instance distanceGraph.instDecidableRelAdj
    (A : Finset Point) (r : ℝ) : DecidableRel (distanceGraph A r).Adj :=
  Classical.decRel _

noncomputable def multiplicity (A : Finset Point) (r : ℝ) : ℕ :=
  (distanceGraph A r).edgeFinset.card

theorem erdos_957 :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : Finset Erdos957.Point) (d₁ dₖ : ℝ),
        Erdos957.IsMinimumDistance A d₁ →
        Erdos957.IsMaximumDistance A dₖ →
        (Erdos957.multiplicity A d₁ : ℝ) * Erdos957.multiplicity A dₖ ≤
          (9 / 8 : ℝ) * (A.card : ℝ) ^ 2 + C * A.card := by
  sorry

end Erdos957
