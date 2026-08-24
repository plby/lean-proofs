/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace UnitFractions

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos299

theorem not_erdos_299 :
    ¬ ∃ a : ℕ → ℕ, StrictMono a ∧
      (∀ i : ℕ, 1 ≤ a i) ∧
      (∃ C : ℕ, ∀ i : ℕ, a (i + 1) - a i ≤ C) ∧
      ∀ S : Finset ℕ, UnitFractions.rec_sum (S.image a) ≠ 1 := by
  sorry

end Erdos299
