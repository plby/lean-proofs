/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos646

def partial_sum (k : ℕ) (p : Fin k → ℕ) (n : ℕ) : Fin k → ZMod 2 :=
  fun i => padicValNat (p i) (Nat.factorial n)

theorem erdos_646 (k : ℕ) (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime) (h_distinct : Function.Injective p) :
  Set.Infinite { n | ∀ i, partial_sum k p n i = 0 } := by
  sorry

end Erdos646
