/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace UnitFractions

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos45

theorem erdos_45 :
    ∀ k : ℕ, 2 ≤ k → ∃ nₖ : ℕ, ∀ c : ℕ → Fin k,
      ∃ D' : Finset ℕ, D' ⊆ ((nₖ.divisors.erase 1).erase nₖ) ∧
        UnitFractions.rec_sum D' = 1 ∧ ∃ a : Fin k, ∀ d ∈ D', c d = a := by
  sorry

end Erdos45
