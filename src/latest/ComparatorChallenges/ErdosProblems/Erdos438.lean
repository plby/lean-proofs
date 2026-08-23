/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

noncomputable section

namespace Erdos438

open scoped Classical in
def SquareSumFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ IsSquare (a + b)

end Erdos438

namespace Erdos438

open scoped Classical in
noncomputable def candidateSets (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter SquareSumFree

end Erdos438

namespace Erdos438

open scoped Classical in
noncomputable def extremalSize (N : ℕ) : ℕ :=
  (candidateSets N).sup Finset.card

end Erdos438

namespace Erdos438

open scoped Classical in
theorem erdos_438 :
    Tendsto (fun N : ℕ ↦ (extremalSize N : ℝ) / (N : ℝ)) atTop
      (nhds ((11 : ℝ) / 32)) := by
  sorry

end Erdos438

end
