/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos947

def IsExactCoveringSystem (l : List (ℤ × ℕ)) : Prop :=
  (∀ p ∈ l, 0 ≤ p.1 ∧ p.1 < p.2) ∧
  (∀ m : ℤ, ∃! i : Fin l.length, let (a, n) := l.get i; m ≡ a [ZMOD n])

theorem erdos_947
    (l : List (ℤ × ℕ)) (h_exact : IsExactCoveringSystem l)
    (h_distinct : l.Pairwise (fun p q => p.2 ≠ q.2)) (h_len : l.length ≥ 2) : False := by
  sorry

end Erdos947
