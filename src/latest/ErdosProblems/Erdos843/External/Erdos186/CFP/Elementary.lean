/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos843.External.Erdos186.GAP

/-!
# Elementary finite-set identities for the CFP argument

This file contains the bookkeeping lemmas about finite sums and finite
subset-sum sets that are used repeatedly in the Conlon--Fox--Pham part of
the proof of Erdős problem 186.  All statements are exact: in particular,
the subset sums of a disjoint union are the sumset of the two subset-sum
sets, and a partition `B ⊆ A` gives the exact factorization into the parts
`B` and `A \ B`.

The translation and sumset operations below are kept in the `Elementary`
namespace so that this file can be imported independently of the higher
level CFP structures.
-/

namespace Erdos186.CFP.Elementary

open scoped BigOperators

variable {d : ℕ}

/-! ## Sums over elementary finite-set decompositions -/

/-- The sum over a disjoint union is the sum over its two parts. -/
theorem sum_union_of_disjoint
    {A B : Finset (LatticePoint d)} (hAB : Disjoint A B) :
    (∑ x ∈ A ∪ B, x) = (∑ x ∈ A, x) + ∑ x ∈ B, x := by
  exact Finset.sum_union hAB

/-- Splitting off a subset gives an exact sum decomposition. -/
theorem sum_sdiff_add_sum_of_subset
    {A B : Finset (LatticePoint d)} (hBA : B ⊆ A) :
    (∑ x ∈ A \ B, x) + ∑ x ∈ B, x = ∑ x ∈ A, x := by
  exact Finset.sum_sdiff hBA

/-- The same subset/difference decomposition with the two summands in the
order in which a partition is usually written. -/
theorem sum_add_sum_sdiff_of_subset
    {A B : Finset (LatticePoint d)} (hBA : B ⊆ A) :
    (∑ x ∈ B, x) + ∑ x ∈ A \ B, x = ∑ x ∈ A, x := by
  simpa [add_comm] using sum_sdiff_add_sum_of_subset (d := d) hBA

/-- A set is the sum of its intersection with another set and its
complementary part. -/
theorem sum_inter_add_sum_sdiff
    (A B : Finset (LatticePoint d)) :
    (∑ x ∈ A ∩ B, x) + ∑ x ∈ A \ B, x = ∑ x ∈ A, x := by
  simpa [Finset.filter_and, add_comm] using
    (Finset.sum_sdiff (f := fun x : LatticePoint d ↦ x)
      (Finset.inter_subset_left : A ∩ B ⊆ A))

/-- The predicate form of a two-piece partition. -/
theorem sum_filter_add_sum_filter_not
    (A : Finset (LatticePoint d)) (p : LatticePoint d → Prop)
    [DecidablePred p] [DecidablePred fun x ↦ ¬ p x] :
    (∑ x ∈ A.filter p, x) + ∑ x ∈ A.filter (fun x ↦ ¬ p x), x =
      ∑ x ∈ A, x := by
  exact Finset.sum_filter_add_sum_filter_not A p (fun x ↦ x)

/-- Removing a member splits its value off from the total sum. -/
theorem sum_erase_add
    {A : Finset (LatticePoint d)} {a : LatticePoint d} (ha : a ∈ A) :
    (∑ x ∈ A.erase a, x) + a = ∑ x ∈ A, x := by
  exact Finset.sum_erase_add A (fun x ↦ x) ha

/-- Inserting a new point adds that point to the total sum. -/
theorem sum_insert
    {A : Finset (LatticePoint d)} {a : LatticePoint d} (ha : a ∉ A) :
    (∑ x ∈ insert a A, x) = a + ∑ x ∈ A, x := by
  exact Finset.sum_insert ha

/-! ## Translates and finite sumsets -/

/-- Translation of a finite set in the integer lattice. -/
def translate (a : LatticePoint d) (S : Finset (LatticePoint d)) :
    Finset (LatticePoint d) :=
  S.image fun x ↦ a + x

@[simp] theorem mem_translate_iff
    {a z : LatticePoint d} {S : Finset (LatticePoint d)} :
    z ∈ translate a S ↔ ∃ x ∈ S, a + x = z := by
  classical
  constructor
  · intro hz
    obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hz
    exact ⟨x, hx, hxz⟩
  · rintro ⟨x, hx, rfl⟩
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- Translation is monotone. -/
theorem translate_mono
    {a : LatticePoint d} {S T : Finset (LatticePoint d)} (hST : S ⊆ T) :
    translate a S ⊆ translate a T := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := mem_translate_iff.mp hz
  exact mem_translate_iff.mpr ⟨x, hST hx, rfl⟩

/-- Translation preserves cardinality. -/
@[simp] theorem card_translate (a : LatticePoint d)
    (S : Finset (LatticePoint d)) :
    (translate a S).card = S.card := by
  classical
  exact Finset.card_image_of_injective S (add_right_injective a)

/-- Translation by zero fixes a finite set. -/
@[simp] theorem translate_zero (S : Finset (LatticePoint d)) :
    translate 0 S = S := by
  classical
  ext x
  simp [mem_translate_iff]

/-- Successive translations combine by adding their translation vectors. -/
theorem translate_translate (a b : LatticePoint d)
    (S : Finset (LatticePoint d)) :
    translate a (translate b S) = translate (a + b) S := by
  classical
  ext z
  simp only [mem_translate_iff]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp [add_assoc]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨b + x, ⟨x, hx, rfl⟩, by simp [add_assoc]⟩

/-- The sum of all points in a translate. -/
theorem sum_translate (a : LatticePoint d)
    (S : Finset (LatticePoint d)) :
    (∑ x ∈ translate a S, x) = S.card • a + ∑ x ∈ S, x := by
  classical
  rw [translate, Finset.sum_image]
  · rw [Finset.sum_add_distrib]
    simp
  · exact Set.injOn_of_injective (add_right_injective a)

/-- The pointwise sumset of two finite sets. -/
def sumset (S T : Finset (LatticePoint d)) : Finset (LatticePoint d) :=
  S.biUnion fun x ↦ translate x T

@[simp] theorem mem_sumset_iff
    {S T : Finset (LatticePoint d)} {z : LatticePoint d} :
    z ∈ sumset S T ↔ ∃ x ∈ S, ∃ y ∈ T, x + y = z := by
  classical
  simp [sumset, mem_translate_iff]

/-- A sumset is monotone in both arguments. -/
theorem sumset_mono
    {S₁ S₂ T₁ T₂ : Finset (LatticePoint d)}
    (hS : S₁ ⊆ S₂) (hT : T₁ ⊆ T₂) :
    sumset S₁ T₁ ⊆ sumset S₂ T₂ := by
  intro z hz
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_sumset_iff.mp hz
  exact mem_sumset_iff.mpr ⟨x, hS hx, y, hT hy, hxy⟩

/-! ## Elementary facts about subset sums -/

/-- Subset sums are monotone in the underlying finite set. -/
theorem subsetSums_mono
    {A B : Finset (LatticePoint d)} (hAB : A ⊆ B) :
    GAP.subsetSums A ⊆ GAP.subsetSums B := by
  intro z hz
  obtain ⟨S, hSA, hsum⟩ := GAP.mem_subsetSums_iff.mp hz
  exact GAP.mem_subsetSums_iff.mpr ⟨S, hSA.trans hAB, hsum⟩

/-- The sum of the whole underlying set is one of its subset sums. -/
theorem sum_mem_subsetSums (A : Finset (LatticePoint d)) :
    (∑ x ∈ A, x) ∈ GAP.subsetSums A := by
  exact GAP.mem_subsetSums_iff.mpr ⟨A, fun _ hx ↦ hx, rfl⟩

@[simp] theorem subsetSums_empty :
    GAP.subsetSums (∅ : Finset (LatticePoint d)) = {0} := by
  classical
  simp [GAP.subsetSums]

@[simp] theorem subsetSums_singleton (a : LatticePoint d) :
    GAP.subsetSums ({a} : Finset (LatticePoint d)) = {0, a} := by
  classical
  ext z
  simp only [GAP.mem_subsetSums_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨S, hS, rfl⟩
    rcases S.eq_empty_or_nonempty with hSempty | hSne
    · left
      simp [hSempty]
    · right
      have hS' : S = {a} := by
        apply Finset.Subset.antisymm hS
        obtain ⟨x, hx⟩ := hSne
        have hxa : x = a := by simpa using hS hx
        subst x
        simpa using hx
      simp [hS']
  · intro hz
    rcases hz with hz | hz
    · subst z
      exact ⟨∅, by simp, by simp⟩
    · subst z
      exact ⟨{a}, fun _ hx ↦ hx, by simp⟩

/-- Subsets chosen from two disjoint sets can be united without changing
the sum except by addition. -/
theorem add_mem_subsetSums_union_of_disjoint
    {A B : Finset (LatticePoint d)} (hAB : Disjoint A B)
    {x y : LatticePoint d} (hx : x ∈ GAP.subsetSums A)
    (hy : y ∈ GAP.subsetSums B) :
    x + y ∈ GAP.subsetSums (A ∪ B) := by
  obtain ⟨S, hSA, rfl⟩ := GAP.mem_subsetSums_iff.mp hx
  obtain ⟨T, hTB, rfl⟩ := GAP.mem_subsetSums_iff.mp hy
  have hST : Disjoint S T := hAB.mono hSA hTB
  refine GAP.mem_subsetSums_iff.mpr ⟨S ∪ T, ?_, ?_⟩
  · exact Finset.union_subset_union hSA hTB
  · exact Finset.sum_union hST

/-- Exact disjoint-union factorization of finite subset sums. -/
theorem subsetSums_union_of_disjoint
    {A B : Finset (LatticePoint d)} (hAB : Disjoint A B) :
    GAP.subsetSums (A ∪ B) =
      sumset (GAP.subsetSums A) (GAP.subsetSums B) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨S, hS, rfl⟩ := GAP.mem_subsetSums_iff.mp hz
    let SA := S ∩ A
    let SB := S \ A
    have hSA : SA ⊆ A := by
      intro x hx
      exact Finset.mem_inter.mp hx |>.2
    have hSB : SB ⊆ B := by
      intro x hx
      have hx' := Finset.mem_sdiff.mp hx
      rcases Finset.mem_union.mp (hS hx'.1) with hxA | hxB
      · exact False.elim (hx'.2 hxA)
      · exact hxB
    have hpart : SA ∪ SB = S := by
      ext x
      simp [SA, SB]
      tauto
    have hdisj : Disjoint SA SB := by
      rw [Finset.disjoint_left]
      intro x hxSA hxSB
      exact (Finset.mem_sdiff.mp hxSB).2 (Finset.mem_inter.mp hxSA).2
    have hsum :
        (∑ x ∈ S, x) = (∑ x ∈ SA, x) + ∑ x ∈ SB, x := by
      rw [← hpart]
      exact Finset.sum_union hdisj
    rw [hsum]
    exact mem_sumset_iff.mpr
      ⟨∑ x ∈ SA, x, GAP.mem_subsetSums_iff.mpr ⟨SA, hSA, rfl⟩,
        ∑ x ∈ SB, x, GAP.mem_subsetSums_iff.mpr ⟨SB, hSB, rfl⟩, rfl⟩
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_sumset_iff.mp hz
    exact add_mem_subsetSums_union_of_disjoint hAB hx hy

/-- Exact factorization associated to a subset and its set difference. -/
theorem subsetSums_partition
    {A B : Finset (LatticePoint d)} (hBA : B ⊆ A) :
    GAP.subsetSums A =
      sumset (GAP.subsetSums B) (GAP.subsetSums (A \ B)) := by
  calc
    GAP.subsetSums A = GAP.subsetSums (B ∪ (A \ B)) := by
      rw [Finset.union_sdiff_of_subset hBA]
    _ = sumset (GAP.subsetSums B) (GAP.subsetSums (A \ B)) :=
      subsetSums_union_of_disjoint Finset.disjoint_sdiff

/-- Adding a new element either leaves a chosen subset unchanged or adds
the new element to a subset sum of the old set. -/
theorem subsetSums_insert_of_not_mem
    {A : Finset (LatticePoint d)} {a : LatticePoint d} (ha : a ∉ A) :
    GAP.subsetSums (insert a A) =
      GAP.subsetSums A ∪ translate a (GAP.subsetSums A) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨S, hS, hsum⟩ := GAP.mem_subsetSums_iff.mp hz
    by_cases haS : a ∈ S
    · apply Finset.mem_union_right
      apply mem_translate_iff.mpr
      refine ⟨∑ x ∈ S.erase a, x, ?_, ?_⟩
      · apply GAP.mem_subsetSums_iff.mpr
        refine ⟨S.erase a, ?_, rfl⟩
        intro x hx
        have hxne : x ≠ a := (Finset.mem_erase.mp hx).1
        rcases Finset.mem_insert.mp (hS ((Finset.erase_subset a S) hx)) with hxa | hxA
        · exact False.elim (hxne hxa)
        · exact hxA
      · have herase := Finset.sum_erase_add S (fun x ↦ x) haS
        rw [← hsum]
        simpa [add_comm] using herase
    · apply Finset.mem_union_left
      apply GAP.mem_subsetSums_iff.mpr
      refine ⟨S, ?_, hsum⟩
      intro x hx
      rcases Finset.mem_insert.mp (hS hx) with hxa | hxA
      · exact False.elim (haS (hxa ▸ hx))
      · exact hxA
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact subsetSums_mono (Finset.subset_insert a A) hz
    · obtain ⟨y, hy, hya⟩ := mem_translate_iff.mp hz
      obtain ⟨T, hTA, hsum⟩ := GAP.mem_subsetSums_iff.mp hy
      have haT : a ∉ T := fun haT ↦ ha (hTA haT)
      apply GAP.mem_subsetSums_iff.mpr
      refine ⟨insert a T, Finset.insert_subset_insert a hTA, ?_⟩
      rw [Finset.sum_insert haT, hsum, hya]

/-- Insert/erase recursion for the subset sums of a set at one of its
members. -/
theorem subsetSums_eq_erase_union_translate
    {A : Finset (LatticePoint d)} {a : LatticePoint d} (ha : a ∈ A) :
    GAP.subsetSums A = GAP.subsetSums (A.erase a) ∪
      translate a (GAP.subsetSums (A.erase a)) := by
  calc
    GAP.subsetSums A = GAP.subsetSums (insert a (A.erase a)) := by
      rw [Finset.insert_erase ha]
    _ = GAP.subsetSums (A.erase a) ∪
        translate a (GAP.subsetSums (A.erase a)) :=
      subsetSums_insert_of_not_mem (by simp [Finset.mem_erase])

/-- The translated old subset sums are contained in the subset sums after
inserting the translation point. -/
theorem translate_subsetSums_subset_insert
    (A : Finset (LatticePoint d)) (a : LatticePoint d) (ha : a ∉ A) :
    translate a (GAP.subsetSums A) ⊆ GAP.subsetSums (insert a A) := by
  rw [subsetSums_insert_of_not_mem ha]
  exact Finset.subset_union_right

end Erdos186.CFP.Elementary
