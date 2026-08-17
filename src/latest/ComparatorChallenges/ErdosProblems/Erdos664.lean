import Mathlib

open scoped BigOperators ENNReal NNReal
open Finset MeasureTheory ProbabilityTheory

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos664

def LinearFamily {ι α : Type*} [DecidableEq α]
    (A : ι → Finset α) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → #(A i ∩ A j) ≤ 1

end Erdos664

namespace Erdos664

def HitsAll {ι α : Type*} [Fintype ι] [DecidableEq α]
    (A : ι → Finset α) (B : Finset α) : Prop :=
  ∀ i, (B ∩ A i).Nonempty

end Erdos664

namespace Erdos664

def HasUniformTransversalBound (c : ℝ) (K : ℕ) : Prop :=
  ∀ n m : ℕ, ∀ A : Fin m → Finset (Fin n),
    (∀ i, c * Real.sqrt n < #(A i)) →
    LinearFamily A →
    ∃ B : Finset (Fin n), HitsAll A B ∧ ∀ i, #(B ∩ A i) ≤ K

end Erdos664

namespace Erdos664

theorem erdos_664 : ¬∃ K : ℕ, HasUniformTransversalBound (2 / 5 : ℝ) K := by
  sorry

end Erdos664

end
