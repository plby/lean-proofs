/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 356

Adrian Beker proved that a strictly increasing sequence in `[n]` can have a
positive quadratic proportion of distinct consecutive sums.  We formalize his
explicit construction.  Its partial sums are

`p t = t ^ 2 + t / b`,

where eventually we take `b = Nat.sqrt N`.  A finite collision-energy estimate
then gives the result.  The accompanying mathematical proof is `tex/356.tex`.
-/

open scoped BigOperators Topology

namespace Erdos356

open Filter Finset

/-- The set of sums of nonempty consecutive pieces of a finite sequence. -/
def consecutiveSums {k : ℕ} (a : Fin k → ℕ) : Finset ℕ :=
  (((Finset.univ : Finset (Fin k)).product Finset.univ).filter fun uv ↦ uv.1 ≤ uv.2).image
    fun uv ↦ ∑ i ∈ Finset.Icc uv.1 uv.2, a i

/-- The exact formal statement of Erdős Problem 356. -/
def Problem356 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    ∃ k : ℕ, ∃ a : Fin k → ℕ,
      StrictMono a ∧
      (∀ i, 1 ≤ a i ∧ a i ≤ n) ∧
      c * (n : ℝ) ^ 2 ≤ ((consecutiveSums a).card : ℝ)

/-! ## Beker's explicit sequence -/

/-- The partial-sum ruler used in Beker's explicit construction. -/
def partialSum (b t : ℕ) : ℕ := t ^ 2 + t / b

/-- The `i`-th, zero-based, term is the next difference of the partial-sum ruler. -/
def bekerTerm (b i : ℕ) : ℕ := partialSum b (i + 1) - partialSum b i


theorem erdos356 : Problem356 := by
  sorry

end Erdos356
