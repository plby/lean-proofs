/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of the all-N formulation of Erdős Problem 343.
https://www.erdosproblems.com/343

Following the cited source, a locally finite infinite multiset is represented
by a nondecreasing sequence. Distinct indices are distinct occurrences,
including when their values are equal. Infinite multiplicity at one value is
the separate immediate case, since its multiples already form an infinite AP.

The displayed problem asks for a universal linear-density threshold and
requires its counting estimate for every N. With this all-N quantifier, the
threshold C = 1 is enough: the nth term is at most n + 1, so Brown's criterion
shows that every natural number is a finite subset sum.

The stronger published Szemerédi--Vu theorem only assumes the counting bound
for all sufficiently large N. Its proof needs their deep finite sumset theorem;
the distinction and the full published proof chain are documented in
tex/343.tex.
-/
import Mathlib

namespace Erdos343

open scoped BigOperators

/-- Finite subset sums of an infinite multiset represented by indexed occurrences. -/
def SubsetSums (A : ℕ → ℕ) : Set ℕ :=
  {n | ∃ s : Finset ℕ, n = ∑ i ∈ s, A i}

/-- A set contains an infinite arithmetic progression with positive difference. -/
def ContainsInfiniteAP (S : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, a + k * d ∈ S

/-- The occurrence-indexed multiset `A` is subcomplete. -/
def IsSubcomplete (A : ℕ → ℕ) : Prop :=
  ContainsInfiniteAP (SubsetSums A)

/--
There are at least `C * N` occurrences of the multiset with value at most `N`.

The finite set is a set of occurrence indices, so repetitions of a value are
counted separately. Finite witnesses also make the definition meaningful when
a value has infinitely many occurrences.
-/
def HasLinearCountingLowerBound (C : ℕ) (A : ℕ → ℕ) : Prop :=
  ∀ N : ℕ, ∃ s : Finset ℕ, C * N ≤ s.card ∧ ∀ i ∈ s, A i ≤ N

/-- Brown's finite-interval argument for occurrence-indexed subset sums. -/


theorem erdos_343 :
    ∃ C : ℕ, 0 < C ∧ ∀ A : ℕ → ℕ,
      Monotone A →
      (∀ i, 0 < A i) →
      HasLinearCountingLowerBound C A →
      IsSubcomplete A := by
  sorry

end Erdos343
