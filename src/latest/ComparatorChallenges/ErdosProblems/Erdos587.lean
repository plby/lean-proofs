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

/-- A cube-root lower bound for every $N \ge 64$. -/
theorem erdos_587.variants.lower_bound (N : ℕ) (hN : 64 ≤ N) :
    (N : ℝ) ^ (1 / 3 : ℝ) / 4 ≤ (MaxNotSqSum N : ℝ) := by
  sorry

/-- An eventual upper bound of the form $N^{1/3} (\log N)^{O(1)}$. -/
theorem erdos_587.variants.nguyen_vu : ∃ᵉ (O > 0) (O' > 0),
    ∀ᶠ N in Filter.atTop,
      (MaxNotSqSum N : ℝ) ≤
        O' * (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ).log ^ O := by
  sorry

/-- Growth $N^{1/3+o(1)}$, expressed by eventual bounds for every positive $\varepsilon$. -/
theorem erdos_587 (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ (1 / 3 - ε) ≤ (MaxNotSqSum N : ℝ) ∧
        (MaxNotSqSum N : ℝ) ≤ (N : ℝ) ^ (1 / 3 + ε) := by
  sorry

end Erdos587
