/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 298.
https://www.erdosproblems.com/forum/thread/298

Informal authors:
- Thomas Bloom

Formal authors:
- Bhavik Mehta
- Thomas Bloom

URLs:
- https://github.com/b-mehta/unit-fractions
-/
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
-- 'Erdos298.erdos298' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms erdos298_density
-- 'Erdos298.erdos298_density' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos298
