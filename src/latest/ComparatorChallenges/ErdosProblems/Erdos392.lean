/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset Nat Real Multiset Asymptotics

namespace Erdos392

open scoped Classical in
theorem Solution_2 (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ n in .atTop, ∃ (t : ℕ) (a : Fin t → ℕ),
      ∏ i, a i = n.factorial ∧ ∀ i, a i ≤ n ^ 2 ∧
        t ≤ (n / 2) - n / (2 * Real.log n) + ε * n / Real.log n := by
  sorry

end Erdos392
