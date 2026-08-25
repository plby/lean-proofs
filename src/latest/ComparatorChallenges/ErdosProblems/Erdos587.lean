/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos587

/--
`MaxNotSqSum N` is the size of the largest subset `A` of
`{1,...,N}` such that for all non-empty `S ⊆ A`, the sum
`∑ n ∈ S, n` is not a square.
-/
def MaxNotSqSum (N : ℕ) : ℕ :=
  (Finset.Icc 1 N |>.powerset.filter fun A => ∀ S ⊆ A, S ≠ ⊥ →
    ¬ IsSquare (∑ n ∈ S, n)).sup Finset.card

/-- An eventual upper bound of the form $N^{1/3} (\log N)^{O(1)}$. -/
theorem erdos_587.variants.nguyen_vu : ∃ᵉ (O > 0) (O' > 0),
    ∀ᶠ N in Filter.atTop,
      (MaxNotSqSum N : ℝ) ≤
        O' * (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ).log ^ O := by
  sorry

end Erdos587
