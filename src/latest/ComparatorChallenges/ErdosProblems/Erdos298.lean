/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter _root_.Finset

namespace UnitFractions

section

variable (A : Set ℕ)

open scoped Classical in
noncomputable def partial_density (N : ℕ) : ℝ := ((range N).filter fun n ↦ n ∈ A).card / N
noncomputable def upper_density : ℝ := limsup (partial_density A) atTop
noncomputable def lower_density : ℝ := liminf (partial_density A) atTop
def has_density (d : ℝ) : Prop := upper_density A = d ∧ lower_density A = d
variable {A}

end

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos298

theorem erdos_298 (A : Set ℕ) (hA : 0 < UnitFractions.upper_density A) :
    ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ UnitFractions.rec_sum S = 1 := by
  sorry

theorem erdos_298_density (A : Set ℕ) (d : ℝ) (hA : UnitFractions.has_density A d) (hd : 0 < d) :
    ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ UnitFractions.rec_sum S = 1 := by
  sorry

end Erdos298
