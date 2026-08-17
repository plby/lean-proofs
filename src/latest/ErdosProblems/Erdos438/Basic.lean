/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026.
Released under Apache 2.0 license.
-/

import Mathlib

/-!
# Erdős Problem 438: finite extremal definitions

This file gives the exact finite formulation of the square-sum-free problem.
In particular, the two summands are allowed to be equal, as they are in the
sumset `A + A`.
-/

namespace Erdos438

/-- A finite set of natural numbers is square-sum-free when the sum of every
ordered pair of its elements (including a repeated element) is not a square. -/
def SquareSumFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ IsSquare (a + b)

/-- The predicate that `A` is one of the sets considered at cutoff `N`. -/
def admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ SquareSumFree A

/-- All square-sum-free subsets of `{1, ..., N}`. -/
noncomputable def candidateSets (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter SquareSumFree

/-- The largest cardinality of a square-sum-free subset of `{1, ..., N}`. -/
noncomputable def extremalSize (N : ℕ) : ℕ :=
  (candidateSets N).sup Finset.card

@[simp] theorem squareSumFree_empty : SquareSumFree ∅ := by
  simp [SquareSumFree]

@[simp] theorem admissible_empty (N : ℕ) : admissible N ∅ := by
  simp [admissible]

@[simp] theorem mem_candidateSets_iff {N : ℕ} {A : Finset ℕ} :
    A ∈ candidateSets N ↔ admissible N A := by
  classical
  simp [candidateSets, admissible]

theorem candidateSets_nonempty (N : ℕ) : (candidateSets N).Nonempty := by
  exact ⟨∅, mem_candidateSets_iff.mpr (admissible_empty N)⟩

/-- Every admissible set is bounded by the finite extremal value. -/
theorem card_le_extremalSize {N : ℕ} {A : Finset ℕ} (hA : admissible N A) :
    A.card ≤ extremalSize N := by
  exact Finset.le_sup (f := Finset.card) (mem_candidateSets_iff.mpr hA)

/-- The supremum defining `extremalSize` is attained by an admissible set. -/
theorem exists_extremizer (N : ℕ) :
    ∃ A : Finset ℕ, admissible N A ∧ A.card = extremalSize N := by
  obtain ⟨A, hA, hmax⟩ :=
    Finset.exists_mem_eq_sup (candidateSets N) (candidateSets_nonempty N) Finset.card
  exact ⟨A, mem_candidateSets_iff.mp hA, hmax.symm⟩

/-- No admissible set can contain more than the `N` elements of `{1, ..., N}`. -/
theorem extremalSize_le (N : ℕ) : extremalSize N ≤ N := by
  obtain ⟨A, hA, hcard⟩ := exists_extremizer N
  rw [← hcard]
  calc
    A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hA.1
    _ ≤ N := by simp

end Erdos438
