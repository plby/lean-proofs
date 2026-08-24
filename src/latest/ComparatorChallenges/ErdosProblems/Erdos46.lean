/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace UnitFractions

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos46

theorem erdos_46 :
    ∀ {α : Type*} [Finite α] (c : ℤ → α),
      ∃ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n) ∧ UnitFractions.rec_sum S = 1 ∧ ∃ a : α, ∀ n ∈ S, c (n : ℤ) = a := by
  sorry

end Erdos46
