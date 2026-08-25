/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos964

def tau (n : ℕ) : ℕ := (Nat.divisors n).card
def divisor_ratios : Set ℚ :=
  { q | ∃ n : ℕ, n > 0 ∧ q = (tau (n + 1) : ℚ) / (tau n : ℚ) }

theorem erdos_964 :
    Set.Ioi (0 : ℝ) ⊆ closure (Set.image (fun q : ℚ => (q : ℝ)) divisor_ratios) := by
  sorry

end Erdos964
