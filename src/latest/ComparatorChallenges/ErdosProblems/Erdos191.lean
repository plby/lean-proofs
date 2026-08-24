/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos191

abbrev Vertices (n : ℕ) := {x : ℕ // x ∈ Finset.Icc 2 n}

def Monochromatic {α : Type*} (G : SimpleGraph α) (X : Finset α) : Prop :=
  G.IsClique X ∨ G.IsIndepSet X

noncomputable def weight (x : ℕ) : ℝ := (Real.log (x : ℝ))⁻¹

def HasLargeMonochromaticSet (C : ℝ) (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Vertices n), ∃ X : Finset (Vertices n),
    Monochromatic G X ∧ C ≤ ∑ x ∈ X, weight x.1

theorem erdos_191 :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, ∀ n ≥ N, HasLargeMonochromaticSet C n := by
  sorry

end Erdos191
