import Mathlib

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos1213

def intervalSum (A : ℕ → ℕ) (u v : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico u v, A i

end Erdos1213

namespace Erdos1213

def HasEqualIntervalSums (A : ℕ → ℕ) (s : ℕ) : Prop :=
  ∃ u v x y : ℕ,
    u < v ∧ v ≤ s ∧ x < y ∧ y ≤ s ∧ (u, v) ≠ (x, y) ∧
      intervalSum A u v = intervalSum A x y

end Erdos1213

namespace Erdos1213

def erdos_1213 : Prop :=
  ∀ a K : ℕ, 1 ≤ a → 1 ≤ K → ∃ f : ℕ, ∀ (s : ℕ) (A : ℕ → ℕ),
    0 < s →
    A 0 = a →
    (∀ ⦃i j : ℕ⦄, i < j → j < s → A i < A j) →
    (∀ ⦃i : ℕ⦄, i + 1 < s → A (i + 1) - A i ≤ K) →
    f < A (s - 1) →
    HasEqualIntervalSums A s

end Erdos1213

namespace Erdos1213

theorem erdos1213 : erdos_1213 := by
  sorry

end Erdos1213

end
