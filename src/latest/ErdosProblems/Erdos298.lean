/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import UnitFractions.Definitions
import UnitFractions.FinalResults

namespace Erdos298

open UnitFractions

theorem erdos298 (A : Set ℕ) (hA : 0 < upper_density A) :
    ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ rec_sum S = 1 := by
  simpa [rec_sum] using unit_fractions_upper_density A hA

theorem erdos298_density (A : Set ℕ) (d : ℝ) (hA : has_density A d) (hd : 0 < d) :
    ∃ S : Finset ℕ, (S : Set ℕ) ⊆ A ∧ rec_sum S = 1 := by
  have hA' : 0 < upper_density A := by
    rw [hA.1]
    exact hd
  exact erdos298 A hA'

#print axioms erdos298
#print axioms erdos298_density

end Erdos298
