/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos356

/-- The set of sums of nonempty consecutive pieces of a finite sequence. -/
def consecutiveSums {k : ℕ} (a : Fin k → ℕ) : Finset ℕ :=
  (((Finset.univ : Finset (Fin k)).product Finset.univ).filter fun uv ↦ uv.1 ≤ uv.2).image
    fun uv ↦ ∑ i ∈ Finset.Icc uv.1 uv.2, a i

/-! ## Beker's explicit sequence -/

theorem erdos_356 :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∃ k : ℕ, ∃ a : Fin k → ℕ,
        StrictMono a ∧
        (∀ i, 1 ≤ a i ∧ a i ≤ n) ∧
        c * (n : ℝ) ^ 2 ≤ ((consecutiveSums a).card : ℝ) := by
  sorry

end Erdos356
