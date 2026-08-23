/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/- `Real.nthRoot` is the compatibility definition used by the upstream
Formal Conjectures statement; it is not yet in this Mathlib release. -/
namespace Real

noncomputable def nthRoot (n : ℕ) (r : ℝ) : ℝ :=
  if Even n then r ^ (n⁻¹ : ℝ) else SignType.sign r ^ n * abs r ^ (n⁻¹ : ℝ)

end Real

namespace Erdos587

/--
`MaxNotSqSum N` is the size of the largest subset `A` of
`{1,...,N}` such that for all non-empty `S ⊆ A`, the sum
`∑ n ∈ S, n` is not a square.
-/
def MaxNotSqSum (N : ℕ) : ℕ :=
  (Finset.Icc 1 N |>.powerset.filter fun A => ∀ S ⊆ A, S ≠ ⊥ →
    ¬ IsSquare (∑ n ∈ S, n)).sup Finset.card

/-- Nguyen and Vu proved that $|A| \ll N^{1/3} (\log N)^{O(1)}$. -/
theorem erdos_587.variants.nguyen_vu : ∃ᵉ (O > 0) (O' > 0),
    ∀ᶠ N in Filter.atTop,
      (MaxNotSqSum N : ℝ) ≤
        O' * Real.nthRoot 3 N * (N : ℝ).log ^ O := by
  sorry

end Erdos587
