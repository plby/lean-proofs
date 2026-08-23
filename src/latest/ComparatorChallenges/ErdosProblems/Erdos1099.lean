/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

noncomputable section


namespace Erdos1099

open scoped Classical in
def orderedDivisor (n : ℕ) : Fin n.divisors.card ↪o ℕ :=
  n.divisors.orderEmbOfFin rfl

end Erdos1099

namespace Erdos1099

open scoped Classical in
def hAlpha (α : ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1),
    Real.rpow
      (((orderedDivisor n ⟨i.1 + 1, by omega⟩ : ℕ) : ℝ) /
          ((orderedDivisor n ⟨i.1, by omega⟩ : ℕ) : ℝ) - 1)
      α

end Erdos1099

namespace Erdos1099

open scoped Classical in
theorem erdos_1099 (α : ℝ) (hα : 1 < α) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∃ᶠ n : ℕ in atTop, hAlpha α n ≤ C) ∧
      Filter.liminf (hAlpha α) atTop ≤ C := by
  sorry

end Erdos1099

end
