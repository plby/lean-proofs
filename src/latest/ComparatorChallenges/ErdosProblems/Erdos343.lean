/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos343

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
