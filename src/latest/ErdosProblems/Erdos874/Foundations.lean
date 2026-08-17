/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib

/-!
# Erdős Problem 874: foundational definitions

This file gives the literal finite formulation of Problem 874.  Its basic
objects are the layers of sums of exactly `r` distinct elements of a finite
set of integers, Straus admissibility (only positive layers are compared),
the finite family of admissible subsets of `{1, ..., N}`, and its maximum
cardinality `k N`.

The restriction to positive layers matters for arbitrary integer sets.  On
sets of positive integers it is equivalent to saying that equality of two
subset sums determines the cardinality of the two subsets; both versions of
that characterization are recorded below.
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The restricted `r`-fold sum layer of `A`: sums of exactly `r` distinct
elements of `A`.  A finite subset represents the increasing tuple occurring
in the statement of the problem. -/
def restrictedSumset (r : ℕ) (A : Finset ℤ) : Finset ℤ :=
  (A.powersetCard r).image fun B => ∑ x ∈ B, x

/-- Membership in a restricted sum layer, in witness-subset form. -/
lemma mem_restrictedSumset {r : ℕ} {A : Finset ℤ} {z : ℤ} :
    z ∈ restrictedSumset r A ↔
      ∃ B : Finset ℤ, B ⊆ A ∧ B.card = r ∧ ∑ x ∈ B, x = z := by
  simp only [restrictedSumset, Finset.mem_image, Finset.mem_powersetCard]
  constructor
  · rintro ⟨B, ⟨hcard, hsub⟩, rfl⟩
    exact ⟨B, hcard, hsub, rfl⟩
  · rintro ⟨B, hsub, hcard, rfl⟩
    exact ⟨B, ⟨hsub, hcard⟩, rfl⟩

/-- The empty layer consists exactly of the empty sum. -/
@[simp] lemma restrictedSumset_zero (A : Finset ℤ) :
    restrictedSumset 0 A = {0} := by
  ext z
  simp [mem_restrictedSumset]
  constructor <;> intro h <;> exact h.symm

/-- There are no restricted `r`-sums once `r` exceeds the size of `A`. -/
lemma restrictedSumset_eq_empty_of_card_lt {r : ℕ} {A : Finset ℤ}
    (hA : A.card < r) :
    restrictedSumset r A = ∅ := by
  rw [restrictedSumset, Finset.powersetCard_eq_empty.mpr hA]
  simp

/-- Straus admissibility: restricted sum layers of different positive
cardinalities are disjoint. -/
def IsAdmissible (A : Finset ℤ) : Prop :=
  ∀ {r s : ℕ}, 0 < r → 0 < s → r ≠ s →
    Disjoint (restrictedSumset r A) (restrictedSumset s A)

/-- Equality of sums of nonempty subsets of `A` determines their sizes. -/
def HasCardinalityDeterminedNonemptySums (A : Finset ℤ) : Prop :=
  ∀ B : Finset ℤ, B ⊆ A → B.Nonempty →
    ∀ C : Finset ℤ, C ⊆ A → C.Nonempty →
      (∑ x ∈ B, x) = ∑ x ∈ C, x → B.card = C.card

/-- Equality of sums of arbitrary subsets of `A` determines their sizes. -/
def HasCardinalityDeterminedSums (A : Finset ℤ) : Prop :=
  ∀ B : Finset ℤ, B ⊆ A →
    ∀ C : Finset ℤ, C ⊆ A →
      (∑ x ∈ B, x) = ∑ x ∈ C, x → B.card = C.card

/-- Literal admissibility is equivalent to the nonempty subset-sum
cardinality formulation, for every finite set of integers. -/
theorem isAdmissible_iff_card_eq_of_nonempty_sum_eq (A : Finset ℤ) :
    IsAdmissible A ↔ HasCardinalityDeterminedNonemptySums A := by
  constructor
  · intro h B hBA hB C hCA hC hsum
    by_contra hcard
    have hBmem : (∑ x ∈ B, x) ∈ restrictedSumset B.card A :=
      mem_restrictedSumset.mpr ⟨B, hBA, rfl, rfl⟩
    have hCmem : (∑ x ∈ B, x) ∈ restrictedSumset C.card A :=
      mem_restrictedSumset.mpr ⟨C, hCA, rfl, hsum.symm⟩
    exact (Finset.disjoint_left.mp
      (h (Finset.card_pos.mpr hB) (Finset.card_pos.mpr hC) hcard)) hBmem hCmem
  · intro h r s hr hs hrs
    rw [Finset.disjoint_left]
    intro z hzr hzs
    obtain ⟨B, hBA, hBcard, hBsum⟩ := mem_restrictedSumset.mp hzr
    obtain ⟨C, hCA, hCcard, hCsum⟩ := mem_restrictedSumset.mp hzs
    have hB : B.Nonempty := Finset.card_pos.mp (hBcard.symm ▸ hr)
    have hC : C.Nonempty := Finset.card_pos.mp (hCcard.symm ▸ hs)
    apply hrs
    rw [← hBcard, ← hCcard]
    exact h B hBA hB C hCA hC (hBsum.trans hCsum.symm)

/-- A nonempty subset of a positive integer set has strictly positive sum. -/
lemma sum_pos_of_subset {A B : Finset ℤ}
    (hpos : ∀ x ∈ A, 0 < x) (hBA : B ⊆ A) (hB : B.Nonempty) :
    0 < ∑ x ∈ B, x := by
  exact Finset.sum_pos (fun x hx => hpos x (hBA hx)) hB

/-- On positive integer sets, literal admissibility is equivalent to the
arbitrary-subset formulation (the empty subset causes no exception). -/
theorem isAdmissible_iff_card_eq_of_sum_eq {A : Finset ℤ}
    (hpos : ∀ x ∈ A, 0 < x) :
    IsAdmissible A ↔ HasCardinalityDeterminedSums A := by
  rw [isAdmissible_iff_card_eq_of_nonempty_sum_eq]
  constructor
  · intro h B hBA C hCA hsum
    by_cases hB : B.Nonempty
    · by_cases hC : C.Nonempty
      · exact h B hBA hB C hCA hC hsum
      · have hCempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
        have hBpos := sum_pos_of_subset hpos hBA hB
        simp [hCempty] at hsum
        omega
    · have hBempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
      by_cases hC : C.Nonempty
      · have hCpos := sum_pos_of_subset hpos hCA hC
        simp [hBempty] at hsum
        omega
      · have hCempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
        simp [hBempty, hCempty]
  · intro h B hBA hB C hCA hC hsum
    exact h B hBA C hCA hsum

/-- The exact integer interval `{1, ..., N}` used in Problem 874. -/
def ambient (N : ℕ) : Finset ℤ :=
  Finset.Icc 1 (N : ℤ)

@[simp] lemma mem_ambient {N : ℕ} {x : ℤ} :
    x ∈ ambient N ↔ 1 ≤ x ∧ x ≤ (N : ℤ) := by
  simp [ambient]

/-- A member of the finite optimization problem defining `k(N)`. -/
def IsBoundedAdmissible (N : ℕ) (A : Finset ℤ) : Prop :=
  A ⊆ ambient N ∧ IsAdmissible A

/-- The finite family of admissible subsets of `{1, ..., N}`. -/
noncomputable def boundedAdmissibleFamily (N : ℕ) : Finset (Finset ℤ) :=
  (ambient N).powerset.filter IsAdmissible

lemma mem_boundedAdmissibleFamily {N : ℕ} {A : Finset ℤ} :
    A ∈ boundedAdmissibleFamily N ↔ IsBoundedAdmissible N A := by
  simp [boundedAdmissibleFamily, IsBoundedAdmissible]

@[simp] lemma isAdmissible_empty : IsAdmissible (∅ : Finset ℤ) := by
  intro r s hr hs hrs
  have hrCard : (∅ : Finset ℤ).card < r := by simp [hr]
  rw [restrictedSumset_eq_empty_of_card_lt hrCard]
  exact Finset.disjoint_empty_left _

/-- The bounded family is never empty: it contains the empty set. -/
lemma boundedAdmissibleFamily_nonempty (N : ℕ) :
    (boundedAdmissibleFamily N).Nonempty := by
  refine ⟨∅, mem_boundedAdmissibleFamily.mpr ?_⟩
  simp [IsBoundedAdmissible]

/-- `k(N)`, the largest cardinality of an admissible subset of
`{1, ..., N}`. -/
noncomputable def k (N : ℕ) : ℕ :=
  (boundedAdmissibleFamily N).sup Finset.card

/-- Every admissible subset of `{1, ..., N}` has cardinality at most `k N`. -/
lemma card_le_k {N : ℕ} {A : Finset ℤ} (hA : IsBoundedAdmissible N A) :
    A.card ≤ k N := by
  exact Finset.le_sup (f := Finset.card)
    (mem_boundedAdmissibleFamily.mpr hA)

/-- The maximum in the definition of `k N` is attained. -/
theorem exists_boundedAdmissible_card_eq_k (N : ℕ) :
    ∃ A : Finset ℤ, IsBoundedAdmissible N A ∧ A.card = k N := by
  have hmem := Finset.sup_mem_of_nonempty (f := Finset.card)
    (boundedAdmissibleFamily_nonempty N)
  rcases hmem with ⟨A, hA, hcard⟩
  exact ⟨A, mem_boundedAdmissibleFamily.mp hA, hcard⟩

/-- Characterization of `k N` as an attained universal cardinality bound. -/
theorem k_eq_iff {N m : ℕ} :
    k N = m ↔
      (∃ A : Finset ℤ, IsBoundedAdmissible N A ∧ A.card = m) ∧
      (∀ A : Finset ℤ, IsBoundedAdmissible N A → A.card ≤ m) := by
  constructor
  · intro hkm
    obtain ⟨A, hA, hcard⟩ := exists_boundedAdmissible_card_eq_k N
    refine ⟨⟨A, hA, hcard.trans hkm⟩, ?_⟩
    intro B hB
    simpa [hkm] using card_le_k hB
  · rintro ⟨⟨A, hA, hcard⟩, hub⟩
    apply Nat.le_antisymm
    · obtain ⟨B, hB, hBcard⟩ := exists_boundedAdmissible_card_eq_k N
      simpa [← hBcard] using hub B hB
    · simpa [← hcard] using card_le_k hA

/-- Equivalent convenient API: `k N ≤ m` exactly when `m` bounds every
admissible subset of `{1, ..., N}`. -/
theorem k_le_iff {N m : ℕ} :
    k N ≤ m ↔
      ∀ A : Finset ℤ, IsBoundedAdmissible N A → A.card ≤ m := by
  constructor
  · intro hkm A hA
    exact (card_le_k hA).trans hkm
  · intro h
    obtain ⟨A, hA, hcard⟩ := exists_boundedAdmissible_card_eq_k N
    simpa [← hcard] using h A hA

/-- The ambient interval itself bounds `k N`. -/
lemma k_le (N : ℕ) : k N ≤ N := by
  rw [k_le_iff]
  intro A hA
  calc
    A.card ≤ (ambient N).card := Finset.card_le_card hA.1
    _ = N := by simp [ambient]

end

end Erdos874
