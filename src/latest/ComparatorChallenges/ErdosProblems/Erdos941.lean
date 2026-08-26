import Mathlib

namespace Erdos941

theorem erdos_941 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ l : List ℕ, 1 ≤ l.length ∧ l.length ≤ 3 ∧
        (∀ a ∈ l, 0 < a ∧ ∀ p : ℕ, p.Prime → p ∣ a → p ^ 2 ∣ a) ∧ l.sum = n := by
  sorry

end Erdos941
