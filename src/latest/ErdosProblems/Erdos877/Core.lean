/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib

/-!
# Erdős Problem 877: finite definitions

This file defines sum-free subsets of the integer interval `[1, n]`, maximality
relative to a finite ambient set, the corresponding finite families and their
cardinalities.  It also records the elementary API used by the counting proof.

The definition of `SumFree` allows the two summands to coincide.
-/

open Finset

namespace Erdos877

/-- The finite interval `{1, ..., n}`. -/
def interval (n : ℕ) : Finset ℕ :=
  Finset.Icc 1 n

@[simp] theorem mem_interval {n x : ℕ} :
    x ∈ interval n ↔ 1 ≤ x ∧ x ≤ n := by
  simp [interval]

@[simp] theorem interval_card (n : ℕ) :
    (interval n).card = n := by
  simp [interval]

@[simp] theorem interval_zero : interval 0 = ∅ := by
  simp [interval]

/-- A finite set of natural numbers is sum-free when the sum of any two of its
members is not a member.  There is no distinctness condition on the summands. -/
def SumFree (A : Finset ℕ) : Prop :=
  ∀ ⦃b c : ℕ⦄, b ∈ A → c ∈ A → b + c ∉ A

noncomputable instance instDecidableSumFree (A : Finset ℕ) : Decidable (SumFree A) :=
  Classical.propDecidable _

/-- The membership formulation of `SumFree`, matching the equation
`a = b + c` in the problem statement. -/
theorem sumFree_iff_no_solution {A : Finset ℕ} :
    SumFree A ↔
      ∀ ⦃a b c : ℕ⦄, a ∈ A → b ∈ A → c ∈ A → a ≠ b + c := by
  constructor
  · intro h a b c ha hb hc habc
    subst a
    exact h hb hc ha
  · intro h b c hb hc hbc
    exact h hbc hb hc rfl

theorem SumFree.not_mem_add {A : Finset ℕ} (hA : SumFree A)
    {b c : ℕ} (hb : b ∈ A) (hc : c ∈ A) :
    b + c ∉ A :=
  hA hb hc

/-- Sum-freeness is inherited by subsets. -/
protected theorem SumFree.mono {A B : Finset ℕ} (hA : SumFree A) (hBA : B ⊆ A) :
    SumFree B := by
  intro b c hb hc hbc
  exact hA (hBA hb) (hBA hc) (hBA hbc)

@[simp] theorem sumFree_empty : SumFree ∅ := by
  simp [SumFree]

theorem sumFree_singleton_of_pos {x : ℕ} (hx : 0 < x) :
    SumFree {x} := by
  rw [sumFree_iff_no_solution]
  intro a b c ha hb hc habc
  simp only [Finset.mem_singleton] at ha hb hc
  subst a
  subst b
  subst c
  omega

/-- Zero cannot belong to a sum-free set. -/
theorem SumFree.zero_not_mem {A : Finset ℕ} (hA : SumFree A) :
    0 ∉ A := by
  intro hzero
  exact (hA hzero hzero) (by simpa using hzero)

/-- In particular, a sum-free set cannot contain both `x` and `2 * x`. -/
theorem SumFree.two_mul_not_mem {A : Finset ℕ} (hA : SumFree A)
    {x : ℕ} (hx : x ∈ A) :
    2 * x ∉ A := by
  simpa [two_mul] using hA hx hx

/-- `A` is a maximal sum-free subset of the ambient finite set `U`. -/
def MaximalSumFreeIn (U A : Finset ℕ) : Prop :=
  A ⊆ U ∧ SumFree A ∧
    ∀ B : Finset ℕ, B ⊆ U → SumFree B → A ⊆ B → A = B

noncomputable instance instDecidableMaximalSumFreeIn (U A : Finset ℕ) :
    Decidable (MaximalSumFreeIn U A) :=
  Classical.propDecidable _

theorem MaximalSumFreeIn.subset {U A : Finset ℕ} (hA : MaximalSumFreeIn U A) :
    A ⊆ U :=
  hA.1

theorem MaximalSumFreeIn.sumFree {U A : Finset ℕ} (hA : MaximalSumFreeIn U A) :
    SumFree A :=
  hA.2.1

theorem MaximalSumFreeIn.eq_of_subset {U A B : Finset ℕ}
    (hA : MaximalSumFreeIn U A) (hBU : B ⊆ U) (hB : SumFree B)
    (hAB : A ⊆ B) :
    A = B :=
  hA.2.2 B hBU hB hAB

/-- The explicit finite predicate agrees with order-theoretic maximality. -/
theorem maximalSumFreeIn_iff_maximal {U A : Finset ℕ} :
    MaximalSumFreeIn U A ↔
      Maximal (fun B : Finset ℕ ↦ B ⊆ U ∧ SumFree B) A := by
  rw [maximal_iff]
  constructor
  · intro hA
    exact ⟨⟨hA.1, hA.2.1⟩, fun B hB hAB ↦ hA.2.2 B hB.1 hB.2 hAB⟩
  · rintro ⟨hA, hmax⟩
    exact ⟨hA.1, hA.2, fun B hBU hB hAB ↦ hmax ⟨hBU, hB⟩ hAB⟩

theorem maximal_iff_maximalSumFreeIn {U A : Finset ℕ} :
    Maximal (fun B : Finset ℕ ↦ B ⊆ U ∧ SumFree B) A ↔
      MaximalSumFreeIn U A :=
  maximalSumFreeIn_iff_maximal.symm

/-- For the hereditary sum-free property, maximality can be checked by trying
to insert one missing ambient element at a time. -/
theorem maximalSumFreeIn_iff_forall_insert {U A : Finset ℕ} :
    MaximalSumFreeIn U A ↔
      A ⊆ U ∧ SumFree A ∧
        ∀ x ∈ U, x ∉ A → ¬ SumFree (insert x A) := by
  constructor
  · intro hA
    refine ⟨hA.1, hA.2.1, ?_⟩
    intro x hxU hxA hxinsert
    have heq : A = insert x A :=
      hA.2.2 (insert x A) (insert_subset hxU hA.1) hxinsert (subset_insert x A)
    apply hxA
    rw [heq]
    exact mem_insert_self x A
  · rintro ⟨hAU, hAfree, hinsert⟩
    refine ⟨hAU, hAfree, ?_⟩
    intro B hBU hBfree hAB
    apply Finset.Subset.antisymm hAB
    intro x hxB
    by_contra hxA
    have hxU : x ∈ U := hBU hxB
    have hinsertB : insert x A ⊆ B := insert_subset hxB hAB
    exact hinsert x hxU hxA (hBfree.mono hinsertB)

/-- An element is addable to `A` when it is new and adjoining it preserves
sum-freeness. -/
def Addable (A : Finset ℕ) (x : ℕ) : Prop :=
  x ∉ A ∧ SumFree (insert x A)

noncomputable instance instDecidableAddable (A : Finset ℕ) (x : ℕ) :
    Decidable (Addable A x) :=
  Classical.propDecidable _

@[simp] theorem addable_iff {A : Finset ℕ} {x : ℕ} :
    Addable A x ↔ x ∉ A ∧ SumFree (insert x A) :=
  Iff.rfl

theorem Addable.not_mem {A : Finset ℕ} {x : ℕ} (hx : Addable A x) :
    x ∉ A :=
  hx.1

theorem Addable.sumFree_insert {A : Finset ℕ} {x : ℕ} (hx : Addable A x) :
    SumFree (insert x A) :=
  hx.2

theorem addable_of_not_mem_of_sumFree_insert {A : Finset ℕ} {x : ℕ}
    (hxA : x ∉ A) (hx : SumFree (insert x A)) :
    Addable A x :=
  ⟨hxA, hx⟩

theorem MaximalSumFreeIn.not_addable {U A : Finset ℕ}
    (hA : MaximalSumFreeIn U A) {x : ℕ} (hxU : x ∈ U) :
    ¬ Addable A x := by
  intro hx
  have heq : A = insert x A :=
    hA.eq_of_subset (insert_subset hxU hA.subset) hx.sumFree_insert (subset_insert x A)
  exact hx.not_mem (by rw [heq]; exact mem_insert_self x A)

theorem maximalSumFreeIn_iff_no_addable {U A : Finset ℕ} :
    MaximalSumFreeIn U A ↔
      A ⊆ U ∧ SumFree A ∧ ∀ x ∈ U, ¬ Addable A x := by
  rw [maximalSumFreeIn_iff_forall_insert]
  constructor
  · rintro ⟨hAU, hA, hinsert⟩
    refine ⟨hAU, hA, ?_⟩
    intro x hxU hxadd
    exact hinsert x hxU hxadd.not_mem hxadd.sumFree_insert
  · rintro ⟨hAU, hA, hadd⟩
    refine ⟨hAU, hA, ?_⟩
    intro x hxU hxA hxinsert
    exact hadd x hxU ⟨hxA, hxinsert⟩

/-- All sum-free subsets of `{1, ..., n}`. -/
noncomputable def sumFreeSets (n : ℕ) : Finset (Finset ℕ) :=
  (interval n).powerset.filter SumFree

/-- All maximal sum-free subsets of `{1, ..., n}`. -/
noncomputable def maximalSumFreeSets (n : ℕ) : Finset (Finset ℕ) :=
  (interval n).powerset.filter (MaximalSumFreeIn (interval n))

@[simp] theorem mem_sumFreeSets {n : ℕ} {A : Finset ℕ} :
    A ∈ sumFreeSets n ↔ A ⊆ interval n ∧ SumFree A := by
  classical
  simp [sumFreeSets]

@[simp] theorem mem_maximalSumFreeSets {n : ℕ} {A : Finset ℕ} :
    A ∈ maximalSumFreeSets n ↔ MaximalSumFreeIn (interval n) A := by
  classical
  constructor
  · intro hA
    exact (Finset.mem_filter.mp hA).2
  · intro hA
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA.subset, hA⟩

theorem maximalSumFreeSets_subset_sumFreeSets (n : ℕ) :
    maximalSumFreeSets n ⊆ sumFreeSets n := by
  intro A hA
  have hmax : MaximalSumFreeIn (interval n) A := mem_maximalSumFreeSets.mp hA
  exact mem_sumFreeSets.mpr ⟨hmax.subset, hmax.sumFree⟩

/-- The number `f(n)` of all sum-free subsets of `{1, ..., n}`. -/
noncomputable def sumFreeCount (n : ℕ) : ℕ :=
  (sumFreeSets n).card

/-- The number `f_m(n)` of maximal sum-free subsets of `{1, ..., n}`. -/
noncomputable def maximalSumFreeCount (n : ℕ) : ℕ :=
  (maximalSumFreeSets n).card

/-- Traditional notation for the number of all sum-free sets. -/
noncomputable abbrev f : ℕ → ℕ := sumFreeCount

/-- Traditional notation for the number of maximal sum-free sets. -/
noncomputable abbrev f_m : ℕ → ℕ := maximalSumFreeCount

theorem maximalSumFreeCount_le_sumFreeCount (n : ℕ) :
    maximalSumFreeCount n ≤ sumFreeCount n := by
  exact Finset.card_le_card (maximalSumFreeSets_subset_sumFreeSets n)

theorem sumFreeCount_le_two_pow (n : ℕ) :
    sumFreeCount n ≤ 2 ^ n := by
  calc
    sumFreeCount n ≤ ((interval n).powerset).card := by
      exact Finset.card_filter_le _ _
    _ = 2 ^ (interval n).card := Finset.card_powerset _
    _ = 2 ^ n := by rw [interval_card]

theorem maximalSumFreeCount_le_two_pow (n : ℕ) :
    maximalSumFreeCount n ≤ 2 ^ n :=
  (maximalSumFreeCount_le_sumFreeCount n).trans (sumFreeCount_le_two_pow n)

/-- Every sum-free subset of a finite ambient set extends to a maximal one. -/
theorem exists_maximalSumFreeIn_superset {U A : Finset ℕ}
    (hAU : A ⊆ U) (hA : SumFree A) :
    ∃ M : Finset ℕ, MaximalSumFreeIn U M ∧ A ⊆ M := by
  classical
  let candidates : Finset (Finset ℕ) := U.powerset.filter SumFree
  have hAcandidates : A ∈ candidates := by
    simp [candidates, hAU, hA]
  obtain ⟨M, hAM, hM⟩ := candidates.exists_le_maximal hAcandidates
  refine ⟨M, ?_, hAM⟩
  rw [maximalSumFreeIn_iff_maximal, maximal_iff]
  refine ⟨?_, ?_⟩
  · simpa [candidates] using hM.1
  · intro B hB hMB
    exact hM.eq_of_le (by simpa [candidates] using hB) hMB

theorem exists_maximalSumFreeIn (U : Finset ℕ) :
    ∃ M : Finset ℕ, MaximalSumFreeIn U M := by
  obtain ⟨M, hM, _⟩ :=
    exists_maximalSumFreeIn_superset (U := U) (A := ∅) (empty_subset U) sumFree_empty
  exact ⟨M, hM⟩

theorem maximalSumFreeSets_nonempty (n : ℕ) :
    (maximalSumFreeSets n).Nonempty := by
  obtain ⟨M, hM⟩ := exists_maximalSumFreeIn (interval n)
  exact ⟨M, mem_maximalSumFreeSets.mpr hM⟩

theorem maximalSumFreeCount_pos (n : ℕ) :
    0 < maximalSumFreeCount n := by
  exact Finset.card_pos.mpr (maximalSumFreeSets_nonempty n)

end Erdos877
