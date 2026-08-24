/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

/-!
# Erdős Problem 851

The formulation uses lower density.
-/

namespace Set

@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

end Set

namespace Erdos851

def TwoPowAddSet (r : ℕ) : Set ℕ :=
  {(2 ^ k + n) | (k : ℕ) (n : ℕ) (_ : n.primeFactors.card ≤ r)}

/-- For every positive error below one, integers representable as a power of
two plus a number with boundedly many distinct prime factors have lower
density at least `1 - ε`. -/
theorem erdos_851 (ε : ℝ) (hε : ε ∈ Set.Ioo 0 1) :
    ∃ r : ℕ, 1 - ε ≤ (TwoPowAddSet r).lowerDensity := by
  sorry
