import Mathlib

namespace Erdos283

open Filter Polynomial Finset

def Condition (p : ℤ[X]) : Prop :=
  p.leadingCoeff > 0 → ¬ (∃ d ≥ 2, ∀ n ≥ 1, d ∣ p.eval n) →
    ∀ᶠ m in atTop, ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
      1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
      m = ∑ i ∈ Finset.Icc 1 (Fin.last k), p.eval (n i)
end Erdos283


open Filter Polynomial Finset

namespace Erdos283

open scoped Classical in
theorem erdos_283 :
    True ↔ ∀ p : ℤ[X], Condition p := by
  sorry

end Erdos283
