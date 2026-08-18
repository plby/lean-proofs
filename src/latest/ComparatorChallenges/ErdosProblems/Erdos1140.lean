import Mathlib

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos1140

def Good (n : ℕ) : Prop :=
  0 < n ∧ ∀ x : ℕ, 2 * x ^ 2 < n → Nat.Prime (n - 2 * x ^ 2)

end Erdos1140

namespace Erdos1140

theorem erdos_1140 : Set.Finite {n : ℕ | Good n} := by
  sorry

end Erdos1140

end
