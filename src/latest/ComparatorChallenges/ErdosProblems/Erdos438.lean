/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos438

def SquareSumFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ IsSquare (a + b)

noncomputable def candidateSets (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter SquareSumFree

noncomputable def extremalSize (N : ℕ) : ℕ :=
  (candidateSets N).sup Finset.card

theorem erdos_438 :
    Tendsto (fun N : ℕ ↦ (extremalSize N : ℝ) / (N : ℝ)) atTop
      (nhds ((11 : ℝ) / 32)) := by
  sorry

end Erdos438
