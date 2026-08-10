import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos453

def erdos_453 : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∃ i : ℕ, i < n ∧
      (Nat.nth Nat.Prime n) ^ (2 : ℕ) <
        (Nat.nth Nat.Prime (n + i)) * (Nat.nth Nat.Prime (n - i))
end Erdos453

attribute [local instance] Classical.propDecidable

theorem Erdos453.not_erdos_453 :
    Not Erdos453.erdos_453
  := by
  sorry
