/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos384

/-- The exceptional coefficient occurs at both symmetric parameter pairs. -/
def IsErdos384Exception (n k : ℕ) : Prop :=
  n = 7 ∧ (k = 3 ∨ k = 4)

/-- The exact strict formulation displayed on the Erdős Problems page.

The inequality `2 * p < n` expresses `p < n / 2` over the rationals without
using truncated natural-number division. -/
def Erdos384StrictStatement : Prop :=
  ∀ n k : ℕ, 1 < k → k < n - 1 → ¬ IsErdos384Exception n k →
    ∃ p : ℕ, p.Prime ∧ p ∣ Nat.choose n k ∧ 2 * p < n

/-- The numerical value of the exceptional symmetric binomial coefficients. -/

theorem erdos384_strict_statement_false : ¬ Erdos384StrictStatement := by
  sorry

end Erdos384
