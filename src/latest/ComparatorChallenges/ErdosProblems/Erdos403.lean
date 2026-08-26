/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

namespace Erdos403

theorem erdos_403 :
    {p : ℕ × Finset ℕ | (∀ a ∈ p.2, 0 < a) ∧ 2 ^ p.1 = p.2.sum Nat.factorial}.Finite := by
  sorry

end Erdos403
