/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 880

Hegyvári, Hennecart, and Plagne proved that the sums of at most two
distinct elements of an additive basis of order two have eventual gaps at
most two, while for every order at least three there is an additive basis
whose corresponding restricted sumset has unbounded gaps.

The detailed mathematical reconstruction and Leanization plan are in
`tex/880.tex`.  The counterexample below is the linear-spike variant of
the block construction proved there.
-/

open Filter

namespace Erdos880

open scoped BigOperators

/-- `n` is a sum of at most `k` (not necessarily distinct) elements of `A`. -/
def UnrestrictedSum (A : Set ℕ) (k n : ℕ) : Prop :=
  ∃ l : List ℕ, l.length ≤ k ∧ (∀ a ∈ l, a ∈ A) ∧ l.sum = n

/-- Sums of at most `k` pairwise distinct elements of `A`. -/
def restrictedSums (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | ∃ s : Finset ℕ, (s : Set ℕ) ⊆ A ∧ s.card ≤ k ∧ ∑ a ∈ s, a = n}

/-- An infinite asymptotic additive basis whose least unrestricted order is `k`. -/
def IsAdditiveBasisOfOrder (A : Set ℕ) (k : ℕ) : Prop :=
  A.Infinite ∧
    (∀ᶠ n in atTop, UnrestrictedSum A k n) ∧
    ∀ j < k, ¬∀ᶠ n in atTop, UnrestrictedSum A j n

/-- The increasing enumeration of a set of naturals.  It has its intended
meaning whenever the set is infinite. -/
noncomputable def enum (B : Set ℕ) (n : ℕ) : ℕ := Nat.nth (fun m ↦ m ∈ B) n

/-- The exact discrete meaning of `b_(n+1) - b_n = O(1)`. -/
def HasBoundedGaps (B : Set ℕ) : Prop :=
  ∃ C, ∀ n, enum B (n + 1) - enum B n ≤ C

/-- A sharp eventual bound for the consecutive gaps. -/
def EventuallyGapAtMost (B : Set ℕ) (C : ℕ) : Prop :=
  ∀ᶠ n in atTop, enum B (n + 1) - enum B n ≤ C

theorem erdos_880 :
    (∀ A : Set ℕ, IsAdditiveBasisOfOrder A 2 →
      HasBoundedGaps (restrictedSums A 2)) ∧
    (∀ h : ℕ, 3 ≤ h → ∃ A : Set ℕ,
      IsAdditiveBasisOfOrder A h ∧ ¬HasBoundedGaps (restrictedSums A h)) := by
  sorry

end Erdos880
