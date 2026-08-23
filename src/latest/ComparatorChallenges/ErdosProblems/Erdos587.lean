import Mathlib

namespace Erdos438

def SquareSumFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ IsSquare (a + b)

def admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ SquareSumFree A

noncomputable def candidateSets (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter SquareSumFree

noncomputable def extremalSize (N : ℕ) : ℕ :=
  (candidateSets N).sup Finset.card

end Erdos438

open Filter

namespace Erdos587

abbrev SquareSumFree (A : Finset ℕ) : Prop :=
  Erdos438.SquareSumFree A

abbrev admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  Erdos438.admissible N A

noncomputable abbrev extremalSize (N : ℕ) : ℕ :=
  Erdos438.extremalSize N

theorem erdos_587 :
    Tendsto (fun N : ℕ ↦ (extremalSize N : ℝ) / (N : ℝ)) atTop
      (nhds ((11 : ℝ) / 32)) := by
  sorry

end Erdos587
