import Mathlib

namespace Erdos296

open Finset Filter

noncomputable section

def recipSum (A : Finset ℕ) : ℚ :=
  ∑ n ∈ A, (1 : ℚ) / n

def HasDisjointUnitDecomps (N k : ℕ) : Prop :=
  ∃ f : Fin k → Finset ℕ,
    (∀ i, f i ⊆ Icc 1 N) ∧
    (∀ i, recipSum (f i) = 1) ∧
    (∀ i j : Fin k, i ≠ j → Disjoint (f i) (f j))
end
end Erdos296

attribute [local instance] Classical.propDecidable

open Finset Filter

namespace Erdos296

theorem erdos296 :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N : ℕ in atTop,
      HasDisjointUnitDecomps N ⌊ c * Real.log N ⌋₊ := by
  sorry

end Erdos296
