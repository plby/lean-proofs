/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos175

open Nat

/-- The central binomial coefficient. -/
def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

/-- Every central binomial coefficient is positive. -/


theorem erdos_175 {n : ℕ} (hn : 5 ≤ n) :
    ¬ Squarefree (Nat.choose (2 * n) n) := by
  sorry

end Erdos175
