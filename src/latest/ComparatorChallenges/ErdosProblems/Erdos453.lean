/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

theorem Erdos453.not_erdos_453 :
    Not (∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ i : ℕ, i < n ∧
        (Nat.nth Nat.Prime n) ^ (2 : ℕ) <
          (Nat.nth Nat.Prime (n + i)) * (Nat.nth Nat.Prime (n - i))) := by
  sorry
