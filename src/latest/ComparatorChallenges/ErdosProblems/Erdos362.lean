import Mathlib

open scoped BigOperators
open Finset

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Erdos362

def subsetSumFiber (A : Finset ℕ) (t : ℕ) : Finset (Finset ℕ) :=
  A.powerset.filter fun S ↦ ∑ a ∈ S, a = t

end Erdos362

namespace Erdos362

def fixedCardSubsetSumFiber (A : Finset ℕ) (l t : ℕ) : Finset (Finset ℕ) :=
  (A.powersetCard l).filter fun S ↦ ∑ a ∈ S, a = t

end Erdos362

namespace Erdos362

def IndexedScalarBound (C : ℝ) : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (w : α → ℕ), Function.Injective w →
    (∀ i, 0 < w i) → 1 ≤ Fintype.card α → ∀ b t : ℕ,
      (((Finset.univ.powerset.filter fun R ↦ b + ∑ i ∈ R, w i = t).card : ℝ) ≤
        C * (2 : ℝ) ^ Fintype.card α / Real.sqrt (Fintype.card α) ^ 3)

def Erdos362Statement : Prop :=
  (∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℕ), A.Nonempty → ∀ t : ℕ,
      ((subsetSumFiber A t).card : ℝ) ≤
        C * (2 : ℝ) ^ A.card / Real.sqrt (A.card : ℝ) ^ 3) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℕ), A.Nonempty → ∀ l t : ℕ,
      ((fixedCardSubsetSumFiber A l t).card : ℝ) ≤
        C * (2 : ℝ) ^ A.card / (A.card : ℝ) ^ 2)

end Erdos362

namespace Erdos362

theorem erdos_362 : Erdos362Statement := by
  sorry

end Erdos362

end
