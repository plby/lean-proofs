/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1140

def Good (n : ℕ) : Prop :=
  0 < n ∧ ∀ x : ℕ, 2 * x ^ 2 < n → Nat.Prime (n - 2 * x ^ 2)

theorem not_erdos_1140 : Set.Finite {n : ℕ | Good n} := by
  sorry

end Erdos1140
