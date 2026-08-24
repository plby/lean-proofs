/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Polynomial

namespace Erdos283

def Condition (p : ℤ[X]) : Prop :=
  p.leadingCoeff > 0 → ¬ (∃ d ≥ 2, ∀ n ≥ 1, d ∣ p.eval n) →
    ∀ᶠ m in atTop, ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
      1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
      m = ∑ i ∈ Finset.Icc 1 (Fin.last k), p.eval (n i)

theorem erdos_283 :
    ∀ p : ℤ[X], Condition p := by
  sorry

end Erdos283
