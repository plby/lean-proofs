/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib


namespace Erdos399

open scoped Classical in
theorem erdos_399 :
    ∃ (n x y k : ℕ), 1 < x * y ∧ 2 < k ∧
      (Nat.factorial n = x ^ k + y ^ k ∨ Nat.factorial n + y ^ k = x ^ k) := by
  sorry

end Erdos399
