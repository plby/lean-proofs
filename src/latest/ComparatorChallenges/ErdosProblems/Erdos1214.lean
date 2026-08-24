/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1214

theorem erdos_1214 :
    ∀ x y : ℕ, x ≥ 1 → y ≥ 1 →
      (∀ n : ℕ, n ≥ 1 →
        {p : ℕ | p.Prime ∧ p ∣ x ^ n - 1} =
          {p : ℕ | p.Prime ∧ p ∣ y ^ n - 1}) →
      x = y := by
  sorry

end Erdos1214
