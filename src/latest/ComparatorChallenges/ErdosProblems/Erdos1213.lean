/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1213

def intervalSum (A : ℕ → ℕ) (u v : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico u v, A i

def HasEqualIntervalSums (A : ℕ → ℕ) (s : ℕ) : Prop :=
  ∃ u v x y : ℕ,
    u < v ∧ v ≤ s ∧ x < y ∧ y ≤ s ∧ (u, v) ≠ (x, y) ∧
      intervalSum A u v = intervalSum A x y

theorem erdos_1213 :
    ∀ a K : ℕ, 1 ≤ a → 1 ≤ K → ∃ f : ℕ, ∀ (s : ℕ) (A : ℕ → ℕ),
      0 < s →
      A 0 = a →
      (∀ ⦃i j : ℕ⦄, i < j → j < s → A i < A j) →
      (∀ ⦃i : ℕ⦄, i + 1 < s → A (i + 1) - A i ≤ K) →
      f < A (s - 1) →
      Erdos1213.HasEqualIntervalSums A s := by
  sorry

end Erdos1213
