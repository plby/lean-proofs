/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos384

/-- The exceptional coefficient occurs at both symmetric parameter pairs. -/
def IsErdos384Exception (n k : ℕ) : Prop :=
  n = 7 ∧ (k = 3 ∨ k = 4)

theorem not_erdos_384 :
    ¬ (∀ n k : ℕ, 1 < k → k < n - 1 → ¬ IsErdos384Exception n k →
      ∃ p : ℕ, p.Prime ∧ p ∣ Nat.choose n k ∧ 2 * p < n) := by
  sorry

end Erdos384
