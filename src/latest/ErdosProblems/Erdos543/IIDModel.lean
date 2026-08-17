/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, ChatGPT
-/

import ErdosProblems.Erdos543.Incidence
import ErdosProblems.Erdos543.Model
import ErdosProblems.Erdos543.FiniteProbability

/-!
# The independent subset-sum model

This file packages the finite independent model used in the Ma--Tang proof of
Erdős Problem 543.  A sample is a function `Fin k → G`, hence an ordered
`k`-tuple of independent uniform elements of the finite additive group `G`.
Indexed subset sums remember the coordinates of the tuple, even when two
coordinates have the same value.

The representation count of a nonzero target is indexed by
`NonemptyIndexSet k` from `Incidence`.  The target zero needs no such
representation because it is always represented by the empty index set.
Consequently indexed completeness is exactly the assertion that the number
of missed nonzero targets is zero.

Finally, forgetting repetitions sends a tuple to its underlying `Finset`.
Every subset sum of that underlying set can be lifted to an indexed subset
sum by choosing one coordinate above each selected value.  This gives the
event, cardinality, and uniform-probability containments used when passing
from ordinary subset completeness to the independent model.
-/

open scoped BigOperators
open Finset

namespace Erdos543.IIDModel

attribute [local instance] Classical.propDecidable

/-! ## Samples, underlying sets, and indexed sums -/

/-- The sample space of ordered `k`-tuples in `G`. -/
abbrev IIDSpace (G : Type*) (k : ℕ) := Fin k → G

/-- The set of values occurring in an independent sample, with repetitions
forgotten. -/
def underlyingSet {G : Type*} [DecidableEq G] {k : ℕ}
    (a : IIDSpace G k) : Finset G :=
  Finset.univ.image a

@[simp] theorem mem_underlyingSet {G : Type*} [DecidableEq G] {k : ℕ}
    {a : IIDSpace G k} {x : G} :
    x ∈ underlyingSet a ↔ ∃ i : Fin k, a i = x := by
  simp [underlyingSet]

@[simp] theorem card_iidSpace (G : Type*) [Fintype G] (k : ℕ) :
    Fintype.card (IIDSpace G k) = Fintype.card G ^ k := by
  simp [IIDSpace]

/-- The sum over a selected set of coordinates of an independent sample. -/
def indexedSum {G : Type*} [AddCommMonoid G] {k : ℕ}
    (a : IIDSpace G k) (S : Finset (Fin k)) : G :=
  ∑ i ∈ S, a i

@[simp] theorem indexedSum_empty {G : Type*} [AddCommMonoid G] {k : ℕ}
    (a : IIDSpace G k) : indexedSum a ∅ = 0 := by
  simp [indexedSum]

/-! ## Hits, misses, and indexed completeness -/

/-- The number of nonempty indexed subsets whose sum is `x`. -/
noncomputable def hitCount {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {k : ℕ} (a : IIDSpace G k) (x : G) : ℕ :=
  (Finset.univ.filter fun S : NonemptyIndexSet k ↦
    indexedSum a (S : Finset (Fin k)) = x).card

theorem hitCount_ne_zero_iff {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {k : ℕ} (a : IIDSpace G k) (x : G) :
    hitCount a x ≠ 0 ↔
      ∃ S : NonemptyIndexSet k, indexedSum a (S : Finset (Fin k)) = x := by
  classical
  simp [hitCount]

theorem hitCount_eq_zero_iff {G : Type*} [AddCommMonoid G] [DecidableEq G]
    {k : ℕ} (a : IIDSpace G k) (x : G) :
    hitCount a x = 0 ↔
      ∀ S : NonemptyIndexSet k, indexedSum a (S : Finset (Fin k)) ≠ x := by
  classical
  simp [hitCount]

/-- The number of nonzero group elements not represented by any nonempty
indexed subset sum. -/
noncomputable def missedNonzeroCount
    {G : Type*} [AddCommMonoid G] [Fintype G] {k : ℕ}
    (a : IIDSpace G k) : ℕ :=
  ((Finset.univ.erase (0 : G)).filter fun x ↦ hitCount a x = 0).card

/-- Every group element is the sum over some set of coordinates of the
sample.  In particular, zero is witnessed by the empty coordinate set. -/
def IndexedComplete {G : Type*} [AddCommMonoid G] {k : ℕ}
    (a : IIDSpace G k) : Prop :=
  ∀ x : G, ∃ S : Finset (Fin k), indexedSum a S = x

/-- Indexed completeness can be tested using only nonzero targets and
nonempty coordinate sets. -/
theorem indexedComplete_iff_nonzero_hit
    {G : Type*} [AddCommMonoid G] [DecidableEq G] {k : ℕ}
    (a : IIDSpace G k) :
    IndexedComplete a ↔ ∀ x : G, x ≠ 0 → hitCount a x ≠ 0 := by
  constructor
  · intro h x hx
    obtain ⟨S, hS⟩ := h x
    have hSne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hEmpty
      subst S
      exact hx (by simpa using hS.symm)
    rw [hitCount_ne_zero_iff]
    exact ⟨⟨S, hSne⟩, hS⟩
  · intro h x
    by_cases hx : x = 0
    · exact ⟨∅, by simp [hx, indexedSum]⟩
    · obtain ⟨S, hS⟩ := (hitCount_ne_zero_iff a x).mp (h x hx)
      exact ⟨S, hS⟩

/-- A tuple is indexed-complete exactly when it misses no nonzero target. -/
theorem indexedComplete_iff_missedNonzeroCount_eq_zero
    {G : Type*} [AddCommMonoid G] [Fintype G] {k : ℕ}
    (a : IIDSpace G k) :
    IndexedComplete a ↔ missedNonzeroCount a = 0 := by
  rw [indexedComplete_iff_nonzero_hit]
  constructor
  · intro h
    apply Finset.card_eq_zero.mpr
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true]
    constructor
    · rintro ⟨hx, hzero⟩
      exact False.elim ((h x hx) hzero)
    · simp
  · intro h x hx
    have hempty :
        (Finset.univ.erase (0 : G)).filter (fun y ↦ hitCount a y = 0) = ∅ :=
      Finset.card_eq_zero.mp h
    intro hzero
    have hxmem : x ∈
        (Finset.univ.erase (0 : G)).filter (fun y ↦ hitCount a y = 0) := by
      simp [hx, hzero]
    rw [hempty] at hxmem
    simp at hxmem

/-! ## Lifting ordinary subset sums to indexed subset sums -/

/-- If every value of `S` occurs in the tuple, choose one coordinate over
each value.  The chosen coordinates have the same sum as `S`; the membership
condition is retained to make the induction robust in the presence of
repeated tuple values. -/
theorem exists_indexSet_sum_eq_of_subset_underlyingSet
    {G : Type*} [AddCommMonoid G] [DecidableEq G] {k : ℕ}
    (a : IIDSpace G k) {S : Finset G} (hS : S ⊆ underlyingSet a) :
    ∃ I : Finset (Fin k),
      (∀ i ∈ I, a i ∈ S) ∧ indexedSum a I = ∑ x ∈ S, x := by
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨∅, by simp, by simp [indexedSum]⟩
  | @insert x S hx ih =>
      have hxUnderlying : x ∈ underlyingSet a :=
        hS (Finset.mem_insert_self x S)
      obtain ⟨i, hai⟩ := mem_underlyingSet.mp hxUnderlying
      have hSUnderlying : S ⊆ underlyingSet a := fun y hy ↦
        hS (Finset.mem_insert_of_mem hy)
      obtain ⟨I, hIvalues, hIsum⟩ := ih hSUnderlying
      have hiI : i ∉ I := by
        intro hi
        apply hx
        simpa [hai] using hIvalues i hi
      refine ⟨insert i I, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simp [hai]
        · exact Finset.mem_insert_of_mem (hIvalues j hj)
      · calc
          indexedSum a (insert i I) = a i + indexedSum a I := by
            simp [indexedSum, hiI]
          _ = x + ∑ y ∈ S, y := by rw [hai, hIsum]
          _ = ∑ y ∈ insert x S, y := by simp [hx]

/-- Completeness of the tuple's underlying ordinary set implies indexed
completeness of the tuple. -/
theorem indexedComplete_of_subsetSumComplete_underlyingSet
    {G : Type*} [AddCommGroup G] [Fintype G] {k : ℕ}
    (a : IIDSpace G k) (hcomplete : Model.SubsetSumComplete (underlyingSet a)) :
    IndexedComplete a := by
  intro x
  obtain ⟨S, hS, hsum⟩ := hcomplete x
  obtain ⟨I, _, hI⟩ :=
    exists_indexSet_sum_eq_of_subset_underlyingSet a hS
  exact ⟨I, hI.trans hsum⟩

/-! ## Event, cardinality, and probability containment -/

/-- Independent samples whose underlying ordinary set is subset-sum
complete. -/
noncomputable def underlyingCompleteTuples
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) :
    Finset (IIDSpace G k) :=
  Finset.univ.filter fun a ↦ Model.SubsetSumComplete (underlyingSet a)

/-- Independent samples which are complete when their coordinates are kept
distinctly indexed. -/
noncomputable def indexedCompleteTuples
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) :
    Finset (IIDSpace G k) :=
  Finset.univ.filter IndexedComplete

@[simp] theorem mem_underlyingCompleteTuples
    {G : Type*} [AddCommGroup G] [Fintype G] {k : ℕ}
    {a : IIDSpace G k} :
    a ∈ underlyingCompleteTuples G k ↔
      Model.SubsetSumComplete (underlyingSet a) := by
  simp [underlyingCompleteTuples]

@[simp] theorem mem_indexedCompleteTuples
    {G : Type*} [AddCommGroup G] [Fintype G] {k : ℕ}
    {a : IIDSpace G k} :
    a ∈ indexedCompleteTuples G k ↔ IndexedComplete a := by
  simp [indexedCompleteTuples]

/-- Ordinary completeness after forgetting repetitions is a subevent of
indexed completeness. -/
theorem underlyingCompleteTuples_subset_indexedCompleteTuples
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) :
    underlyingCompleteTuples G k ⊆ indexedCompleteTuples G k := by
  intro a ha
  rw [mem_underlyingCompleteTuples] at ha
  rw [mem_indexedCompleteTuples]
  exact indexedComplete_of_subsetSumComplete_underlyingSet a ha

/-- Cardinality form of the ordinary-to-indexed event containment. -/
theorem card_underlyingCompleteTuples_le_card_indexedCompleteTuples
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) :
    (underlyingCompleteTuples G k).card ≤
      (indexedCompleteTuples G k).card :=
  Finset.card_le_card
    (underlyingCompleteTuples_subset_indexedCompleteTuples G k)

/-- Set-valued ordinary-completeness event on the independent sample space. -/
def underlyingCompleteEvent
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) :
    Set (IIDSpace G k) :=
  {a | Model.SubsetSumComplete (underlyingSet a)}

/-- Set-valued indexed-completeness event on the independent sample space. -/
def indexedCompleteEvent
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) :
    Set (IIDSpace G k) :=
  {a | IndexedComplete a}

/-- Set containment corresponding to the filtered-finset containment above. -/
theorem underlyingCompleteEvent_subset_indexedCompleteEvent
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) :
    underlyingCompleteEvent G k ⊆ indexedCompleteEvent G k := by
  intro a ha
  exact indexedComplete_of_subsetSumComplete_underlyingSet a ha

/-- Uniform-probability form of the ordinary-to-indexed event containment. -/
theorem prob_underlyingCompleteEvent_le_prob_indexedCompleteEvent
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) :
    FiniteProbability.prob (underlyingCompleteEvent G k) ≤
      FiniteProbability.prob (indexedCompleteEvent G k) :=
  FiniteProbability.prob_mono
    (underlyingCompleteEvent_subset_indexedCompleteEvent G k)

end Erdos543.IIDModel
