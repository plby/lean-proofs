/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos362

def subsetSumFiber (A : Finset ℕ) (t : ℕ) : Finset (Finset ℕ) :=
  A.powerset.filter fun S ↦ ∑ a ∈ S, a = t

def fixedCardSubsetSumFiber (A : Finset ℕ) (l t : ℕ) : Finset (Finset ℕ) :=
  (A.powersetCard l).filter fun S ↦ ∑ a ∈ S, a = t

theorem erdos_362 :
    (∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℕ), A.Nonempty → ∀ t : ℕ,
        ((subsetSumFiber A t).card : ℝ) ≤
          C * (2 : ℝ) ^ A.card / Real.sqrt (A.card : ℝ) ^ 3) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℕ), A.Nonempty → ∀ l t : ℕ,
        ((fixedCardSubsetSumFiber A l t).card : ℝ) ≤
          C * (2 : ℝ) ^ A.card / (A.card : ℝ) ^ 2) := by
  sorry

end Erdos362
