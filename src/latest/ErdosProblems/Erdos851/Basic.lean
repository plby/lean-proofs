/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib
import Util.Density

/-!
# Basic definitions for Erdős problem 851

This file isolates the source-faithful representation set so that the
arithmetic, sieve, and density layers can all use it without import cycles.
-/

namespace Erdos851

/-- Integers representable as a power of two plus a natural number having at
most `r` distinct prime divisors. -/
def TwoPowAddSet (r : ℕ) : Set ℕ :=
  {(2 ^ k + n) | (k : ℕ) (n : ℕ) (_ : n.primeFactors.card ≤ r)}

/-- Integers representable as a power of two plus a prime. -/
def twoPowAddPrimeSet : Set ℕ :=
  {(2 ^ k + p) | (k : ℕ) (p : ℕ) (_ : p.Prime)}

@[simp]
theorem mem_twoPowAddSet {r m : ℕ} :
    m ∈ TwoPowAddSet r ↔
      ∃ k n : ℕ, n.primeFactors.card ≤ r ∧ 2 ^ k + n = m := by
  simp only [TwoPowAddSet]
  constructor
  · rintro ⟨k, n, hn, rfl⟩
    exact ⟨k, n, hn, rfl⟩
  · rintro ⟨k, n, hn, rfl⟩
    exact ⟨k, n, hn, rfl⟩

/-- Allowing more distinct prime factors can only enlarge the representable set. -/
theorem twoPowAddSet_mono {r s : ℕ} (hrs : r ≤ s) :
    TwoPowAddSet r ⊆ TwoPowAddSet s := by
  rintro m ⟨k, n, hn, rfl⟩
  exact ⟨k, n, hn.trans hrs, rfl⟩

/-- The classical Romanoff set is contained in the one-prime-factor case. -/
theorem twoPowAddPrimeSet_subset :
    twoPowAddPrimeSet ⊆ TwoPowAddSet 1 := by
  rintro m ⟨k, p, hp, rfl⟩
  exact ⟨k, p, by simp [hp.primeFactors], rfl⟩

end Erdos851
