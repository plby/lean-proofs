/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos392

theorem erdos_392 (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ n in .atTop, ∃ (t : ℕ) (a : Fin t → ℕ),
      ∏ i, a i = n.factorial ∧ ∀ i, a i ≤ n ^ 2 ∧
        t ≤ (n / 2) - n / (2 * Real.log n) + ε * n / Real.log n := by
  sorry

end Erdos392
