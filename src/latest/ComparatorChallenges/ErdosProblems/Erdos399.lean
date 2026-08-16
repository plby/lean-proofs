import Mathlib

attribute [local instance] Classical.propDecidable

namespace Erdos399

theorem erdos_399 : False ↔
    ¬ ∃ (n x y k : ℕ), 1 < x * y ∧ 2 < k ∧
      (Nat.factorial n = x ^ k + y ^ k ∨ Nat.factorial n + y ^ k = x ^ k) := by
  sorry

end Erdos399
