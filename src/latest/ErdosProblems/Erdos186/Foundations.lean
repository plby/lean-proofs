/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib

/-!
# Erdős Problem 186: the finite extremal function

This file gives the literal finite definition of a nonaveraging set and of
the extremal function from Erdős Problem 186.  An averaging witness for
`a ∈ A` is a *set* `S ⊆ A.erase a` of at least two elements whose sum is
`S.card * a`.  Thus the elements being averaged are distinct and do not
include their proposed average.
-/

namespace Erdos186

open Finset

noncomputable section

/-- A finite set of natural numbers is nonaveraging if none of its elements
is the arithmetic mean of a subset of at least two of its other elements.

The equation is written without division, so it is an exact equation in
`Nat`: the mean of `S` is `a` precisely when `S.card * a = S.sum id`. -/
def IsNonaveraging (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ,
    S ⊆ A.erase a → 2 ≤ S.card → S.card * a ≠ S.sum id

/-- Alternate capitalization retained for readability in downstream files. -/
abbrev IsNonAveraging := IsNonaveraging

/-- `A` is an allowed set for Erdős Problem 186 with ambient interval
`{1, …, N}`. -/
def Admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ IsNonaveraging A

/-- The empty set is nonaveraging. -/
@[simp] theorem isNonaveraging_empty : IsNonaveraging (∅ : Finset ℕ) := by
  simp [IsNonaveraging]

/-- A singleton is nonaveraging. -/
@[simp] theorem isNonaveraging_singleton (a : ℕ) : IsNonaveraging {a} := by
  intro b hb S hS hcard
  have hba : b = a := by simpa using hb
  subst b
  have hSsub : S ⊆ (∅ : Finset ℕ) := by simpa using hS
  have hSempty : S = ∅ := Finset.subset_empty.mp hSsub
  subst S
  simp at hcard

/-- The nonaveraging property is inherited by subsets. -/
theorem IsNonaveraging.mono {A B : Finset ℕ} (hA : IsNonaveraging A)
    (hBA : B ⊆ A) : IsNonaveraging B := by
  intro a ha S hS hcard
  apply hA a (hBA ha) S
  · intro x hx
    have hx' := Finset.mem_erase.mp (hS hx)
    exact Finset.mem_erase.mpr ⟨hx'.1, hBA hx'.2⟩
  · exact hcard

/-- The empty set is admissible for every ambient interval. -/
@[simp] theorem admissible_empty (N : ℕ) : Admissible N ∅ := by
  simp [Admissible]

/-- All subsets over which the finite maximum at `N` is taken. -/
noncomputable def candidateSets (N : ℕ) : Finset (Finset ℕ) :=
  by
    classical
    exact (Finset.Icc 1 N).powerset.filter IsNonaveraging

/-- Membership in `candidateSets N` is exactly admissibility at `N`. -/
@[simp] theorem mem_candidateSets {N : ℕ} {A : Finset ℕ} :
    A ∈ candidateSets N ↔ Admissible N A := by
  simp [candidateSets, Admissible]

/-- The candidate family is nonempty. -/
theorem candidateSets_nonempty (N : ℕ) : (candidateSets N).Nonempty := by
  exact ⟨∅, mem_candidateSets.mpr (admissible_empty N)⟩

/-- `F N` is the maximum cardinality of a nonaveraging subset of
`{1, …, N}`. -/
noncomputable def F (N : ℕ) : ℕ :=
  (candidateSets N).sup Finset.card

/-- Every admissible set has cardinality at most `F N`. -/
theorem card_le_F {N : ℕ} {A : Finset ℕ} (hA : Admissible N A) :
    A.card ≤ F N := by
  exact Finset.le_sup (f := Finset.card) (mem_candidateSets.mpr hA)

/-- A convenience form of `card_le_F` with the two admissibility hypotheses
separated. -/
theorem card_le_F_of_subset {N : ℕ} {A : Finset ℕ}
    (hsub : A ⊆ Finset.Icc 1 N) (hA : IsNonaveraging A) : A.card ≤ F N :=
  card_le_F ⟨hsub, hA⟩

/-- The supremum defining `F N` is attained by an admissible set. -/
theorem exists_extremizer (N : ℕ) :
    ∃ A : Finset ℕ, Admissible N A ∧ A.card = F N := by
  obtain ⟨A, hA, hmax⟩ :=
    (candidateSets N).exists_max_image Finset.card (candidateSets_nonempty N)
  refine ⟨A, mem_candidateSets.mp hA, le_antisymm ?_ ?_⟩
  · exact card_le_F (mem_candidateSets.mp hA)
  · exact Finset.sup_le fun B hB ↦ hmax B hB

/-- Explicit maximum specification, named after the property rather than the
implementation of the candidate family. -/
theorem exists_nonaveraging_card_eq_F (N : ℕ) :
    ∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N ∧ IsNonaveraging A ∧ A.card = F N := by
  obtain ⟨A, hA, hcard⟩ := exists_extremizer N
  exact ⟨A, hA.1, hA.2, hcard⟩

/-- An exact specification of the natural numbers below `F N`. -/
theorem le_F_iff {N m : ℕ} :
    m ≤ F N ↔
      ∃ A : Finset ℕ, Admissible N A ∧ m ≤ A.card := by
  constructor
  · intro hm
    obtain ⟨A, hA, hcard⟩ := exists_extremizer N
    exact ⟨A, hA, hm.trans_eq hcard.symm⟩
  · rintro ⟨A, hA, hm⟩
    exact hm.trans (card_le_F hA)

/-- Enlarging the ambient interval cannot decrease the extremal size. -/
theorem F_mono : Monotone F := by
  intro N M hNM
  obtain ⟨A, hA, hcard⟩ := exists_extremizer N
  have hAsub : A ⊆ Finset.Icc 1 M := by
    intro a ha
    have haIcc := Finset.mem_Icc.mp (hA.1 ha)
    exact Finset.mem_Icc.mpr ⟨haIcc.1, haIcc.2.trans hNM⟩
  rw [← hcard]
  exact card_le_F ⟨hAsub, hA.2⟩

/-- The extremal size is at most the size of its ambient interval. -/
theorem F_le (N : ℕ) : F N ≤ N := by
  obtain ⟨A, hA, hcard⟩ := exists_extremizer N
  rw [← hcard]
  calc
    A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hA.1
    _ = N := by simp

/-- The degenerate ambient interval at zero has extremal size zero. -/
@[simp] theorem F_zero : F 0 = 0 := by
  exact Nat.le_zero.mp (F_le 0)

/-- Every nonempty ambient interval has extremal size at least one. -/
theorem one_le_F {N : ℕ} (hN : 1 ≤ N) : 1 ≤ F N := by
  have hAdmissible : Admissible N {1} := by
    constructor
    · simpa using hN
    · exact isNonaveraging_singleton 1
  simpa using card_le_F hAdmissible

/-- `F N` is positive exactly when the ambient interval is nonempty. -/
@[simp] theorem F_pos_iff {N : ℕ} : 0 < F N ↔ 0 < N := by
  constructor
  · intro hF
    exact lt_of_lt_of_le hF (F_le N)
  · intro hN
    exact one_le_F (Nat.one_le_iff_ne_zero.mpr hN.ne')

end

end Erdos186
