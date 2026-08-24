/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos903

/-- An indexed family of blocks is a pairwise balanced design of index one.
The lower bound of two on block size is part of the standard definition of a
linear space and rules out irrelevant empty or singleton blocks. -/
def PairwiseBalanced {v b : ℕ} (block : Fin b → Finset (Fin v)) : Prop :=
  (∀ i, 2 ≤ (block i).card) ∧
    ∀ x y, x ≠ y → ∃! i, x ∈ block i ∧ y ∈ block i

theorem erdos_903 (p b : ℕ) (hp : IsPrimePow p)
    (block : Fin b → Finset (Fin (p ^ 2 + p + 1)))
    (hpb : PairwiseBalanced block) (hmore : p ^ 2 + p + 1 < b) :
    p ^ 2 + p + 1 + p ≤ b := by
  sorry

end Erdos903
