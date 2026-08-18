/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Basic

/-!
# Pulling a common deviation sum back to an averaging witness

This file records the elementary final step used by the intersection part of
the Pham--Zakharov argument.  The subset-sum sets there are formed after
mapping the original points to their deviations from a proposed mean.  Since
both deviation maps are injective, a subset of either image has a unique
pullback to a subset of the corresponding pool of original points.
-/

namespace Erdos186.PZ

open scoped BigOperators

noncomputable section

/-- Pull a subset-sum witness through an injective map.  The injectivity is
essential: `GAP.subsetSums (A.image e)` uses the distinct values in the image,
whereas the conclusion uses the original points as indices. -/
theorem exists_subset_sum_eq_of_mem_subsetSums_image
    {α β : Type*} [DecidableEq β] [AddCommMonoid β]
    (e : α ↪ β) {A : Finset α} {z : β}
    (hz : z ∈ GAP.subsetSums (A.image e)) :
    ∃ S ⊆ A, ∑ x ∈ S, e x = z := by
  classical
  obtain ⟨T, hT, hsum⟩ := GAP.mem_subsetSums_iff.mp hz
  let S : Finset α := T.preimage e e.injective.injOn
  have hmap : S.map e = T := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      exact Finset.mem_preimage.mp hx
    · intro hy
      obtain ⟨x, hxA, hxy⟩ := Finset.mem_image.mp (hT hy)
      exact Finset.mem_map.mpr
        ⟨x, Finset.mem_preimage.mpr (hxy.symm ▸ hy), hxy⟩
  refine ⟨S, ?_, ?_⟩
  · intro x hx
    have hex : e x ∈ T := by
      rw [← hmap]
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hyA, hy⟩ := Finset.mem_image.mp (hT hex)
    have hyx : y = x := e.injective hy
    simpa [hyx] using hyA
  · rw [← hsum, ← hmap]
    simp

/-- A nonzero element common to the two deviation subset-sum sets yields
nonempty, disjoint subfamilies of original points with equal deviation sums.

The conclusion deliberately retains both equations with `z`; this is the
form needed by `averaging_witness_of_common_deviation_sum`, and it also avoids
losing the information that both selected subfamilies are nonempty. -/
theorem common_subsetSums_deviations_gives_witness {d : ℕ}
    {A₁ A₂ : Finset (LatticePoint d)} {a z : LatticePoint d}
    (hdisj : Disjoint A₁ A₂) (hz : z ≠ 0)
    (hz₁ : z ∈ GAP.subsetSums (A₁.image fun x ↦ x - a))
    (hz₂ : z ∈ GAP.subsetSums (A₂.image fun x ↦ a - x)) :
    ∃ S₁ S₂ : Finset (LatticePoint d),
      S₁.Nonempty ∧ S₂.Nonempty ∧
      S₁ ⊆ A₁ ∧ S₂ ⊆ A₂ ∧ Disjoint S₁ S₂ ∧
      (∑ x ∈ S₁, (x - a)) = z ∧
      (∑ x ∈ S₂, (a - x)) = z := by
  classical
  let e₁ : LatticePoint d ↪ LatticePoint d :=
    ⟨fun x ↦ x - a, sub_left_injective⟩
  let e₂ : LatticePoint d ↪ LatticePoint d :=
    ⟨fun x ↦ a - x, sub_right_injective⟩
  obtain ⟨S₁, hS₁, hsum₁⟩ :=
    exists_subset_sum_eq_of_mem_subsetSums_image e₁ hz₁
  obtain ⟨S₂, hS₂, hsum₂⟩ :=
    exists_subset_sum_eq_of_mem_subsetSums_image e₂ hz₂
  have hS₁ne : S₁.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    subst S₁
    simp at hsum₁
    exact hz hsum₁.symm
  have hS₂ne : S₂.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    subst S₂
    simp at hsum₂
    exact hz hsum₂.symm
  refine ⟨S₁, S₂, hS₁ne, hS₂ne, hS₁, hS₂,
    hdisj.mono hS₁ hS₂, ?_, ?_⟩
  · exact hsum₁
  · exact hsum₂

/-- Directly package a nonzero common deviation subset sum as a forbidden
average in the ambient set. -/
theorem averaging_witness_of_common_subsetSums_deviations {d : ℕ}
    {A A₁ A₂ : Finset (LatticePoint d)} {a z : LatticePoint d}
    (ha : a ∈ A)
    (hA₁ : A₁ ⊆ A.erase a) (hA₂ : A₂ ⊆ A.erase a)
    (hdisj : Disjoint A₁ A₂) (hz : z ≠ 0)
    (hz₁ : z ∈ GAP.subsetSums (A₁.image fun x ↦ x - a))
    (hz₂ : z ∈ GAP.subsetSums (A₂.image fun x ↦ a - x)) :
    ¬ IsBoxNonaveraging A := by
  obtain ⟨S₁, S₂, _hS₁ne, _hS₂ne, hS₁, hS₂, hSdisj,
    hsum₁, hsum₂⟩ :=
    common_subsetSums_deviations_gives_witness hdisj hz hz₁ hz₂
  exact averaging_witness_of_common_deviation_sum ha
    (hS₁.trans hA₁) (hS₂.trans hA₂) hSdisj hz hsum₁ hsum₂

/-- In a nonaveraging set, every common deviation subset sum from two
disjoint pools is zero. -/
theorem common_subsetSums_deviations_eq_zero_of_nonaveraging {d : ℕ}
    {A A₁ A₂ : Finset (LatticePoint d)} {a z : LatticePoint d}
    (hA : IsBoxNonaveraging A) (ha : a ∈ A)
    (hA₁ : A₁ ⊆ A.erase a) (hA₂ : A₂ ⊆ A.erase a)
    (hdisj : Disjoint A₁ A₂)
    (hz₁ : z ∈ GAP.subsetSums (A₁.image fun x ↦ x - a))
    (hz₂ : z ∈ GAP.subsetSums (A₂.image fun x ↦ a - x)) :
    z = 0 := by
  by_contra hz
  exact averaging_witness_of_common_subsetSums_deviations
    ha hA₁ hA₂ hdisj hz hz₁ hz₂ hA

end

end Erdos186.PZ
