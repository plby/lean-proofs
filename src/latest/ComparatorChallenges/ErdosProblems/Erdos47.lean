/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Real

namespace UnitFractions

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos47

theorem erdos_47_quantitative :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      C * ((log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ)) < UnitFractions.rec_sum A →
      ∃ S ⊆ A, UnitFractions.rec_sum S = 1 := by
  sorry

theorem erdos_47 :
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      δ * log N < UnitFractions.rec_sum A →
      ∃ S ⊆ A, UnitFractions.rec_sum S = 1 := by
  sorry

end Erdos47
