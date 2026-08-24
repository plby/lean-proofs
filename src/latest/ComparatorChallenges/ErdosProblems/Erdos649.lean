/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos649

def P (n : ℕ) : ℕ := (n.primeFactors).max.getD 0
def StrangePair (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p ≠ q ∧ ∀ n ≥ 2, P n * P (n + 1) ≠ p * q

theorem erdos_649 : { q | StrangePair 2 q }.Infinite := by
  sorry

end Erdos649
