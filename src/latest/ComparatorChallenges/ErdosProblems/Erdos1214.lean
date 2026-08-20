import Mathlib

open Polynomial

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos1214

theorem erdos_1214 :
    True ↔ ∀ x y : ℕ, x ≥ 1 → y ≥ 1 →
      (∀ n : ℕ, n ≥ 1 →
        {p : ℕ | p.Prime ∧ p ∣ x ^ n - 1} =
          {p : ℕ | p.Prime ∧ p ∣ y ^ n - 1}) →
      x = y := by
  sorry

end Erdos1214

end
