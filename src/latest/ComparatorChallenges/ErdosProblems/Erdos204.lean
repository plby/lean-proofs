/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos204

theorem not_erdos_204 : ¬ ∃ (n : ℕ) (a : ℕ → ℤ),
    let D := {d : ℕ | d ∣ n ∧ d > 1}
    (∀ x : ℤ, ∃ d ∈ D, x ≡ a d [ZMOD d]) ∧
    (∀ d ∈ D, ∀ d' ∈ D, d ≠ d' → (∃ x : ℤ, x ≡ a d [ZMOD d] → x ≡ a d' [ZMOD d']) →
      Nat.gcd d d' = 1) := by
  sorry

end Erdos204
