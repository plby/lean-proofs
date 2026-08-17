import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs

attribute [local instance] Classical.propDecidable

namespace Erdos427

theorem erdos427 (n d : ℕ) (hd : 1 ≤ d) :
    ∃ k, 1 ≤ k ∧
      d ∣ (Finset.range k).sum (fun i => Nat.nth Nat.Prime (n + i)) := by
  sorry

end Erdos427
