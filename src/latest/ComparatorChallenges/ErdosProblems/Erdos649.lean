import Mathlib

namespace Erdos649

def P (n : ℕ) : ℕ := (n.primeFactors).max.getD 0
def StrangePair (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p ≠ q ∧ ∀ n ≥ 2, P n * P (n + 1) ≠ p * q
end Erdos649

attribute [local instance] Classical.propDecidable

namespace Erdos649

theorem infinite_strange_pairs : { q | StrangePair 2 q }.Infinite := by
  sorry

end Erdos649
