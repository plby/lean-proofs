import Mathlib

open scoped BigOperators
open Finset

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Erdos191

abbrev Vertices (n : ℕ) := {x : ℕ // x ∈ Finset.Icc 2 n}

end Erdos191

namespace Erdos191

def Monochromatic {α : Type*} (G : SimpleGraph α) (X : Finset α) : Prop :=
  G.IsClique X ∨ G.IsIndepSet X

end Erdos191

namespace Erdos191

def weight (x : ℕ) : ℝ := (Real.log (x : ℝ))⁻¹

end Erdos191

namespace Erdos191

def HasLargeMonochromaticSet (C : ℝ) (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Vertices n), ∃ X : Finset (Vertices n),
    Monochromatic G X ∧ C ≤ ∑ x ∈ X, weight x.1

end Erdos191

namespace Erdos191

theorem erdos_191 :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, ∀ n ≥ N, HasLargeMonochromaticSet C n := by
  sorry

end Erdos191

end
