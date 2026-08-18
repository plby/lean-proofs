/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.Foundations

/-!
# Erdős Problem 186: the subset-sum criterion

This file proves the elementary bridge from the literal definition of a
nonaveraging set to the subset-sum formulation used by the structural upper
bound.  The subset sums are indexed by the original finite set.  In
particular, no injectivity assumption on the weight function is needed.
-/

namespace Erdos186

open Finset

noncomputable section

/-- All finite `0/1` subset sums of the weights `w x`, with indices restricted
to `A`.  The empty subset contributes zero. -/
def subsetSums {α : Type*} [DecidableEq α] (A : Finset α) (w : α → ℤ) : Finset ℤ :=
  A.powerset.image fun S ↦ S.sum w

@[simp] theorem mem_subsetSums {α : Type*} [DecidableEq α]
    {A : Finset α} {w : α → ℤ} {z : ℤ} :
    z ∈ subsetSums A w ↔ ∃ S : Finset α, S ⊆ A ∧ S.sum w = z := by
  simp [subsetSums]

@[simp] theorem zero_mem_subsetSums {α : Type*} [DecidableEq α]
    (A : Finset α) (w : α → ℤ) :
    0 ∈ subsetSums A w := by
  exact mem_subsetSums.mpr ⟨∅, empty_subset A, by simp⟩

/-- For a proposed mean `a`, these are the subset sums of the upward
deviations `x-a` contributed by indices in `A`. -/
def upperDeviationSums (a : ℕ) (A : Finset ℕ) : Finset ℤ :=
  subsetSums A fun x ↦ (x : ℤ) - (a : ℤ)

/-- For a proposed mean `a`, these are the subset sums of the downward
deviations `a-x` contributed by indices in `A`. -/
def lowerDeviationSums (a : ℕ) (A : Finset ℕ) : Finset ℤ :=
  subsetSums A fun x ↦ (a : ℤ) - (x : ℤ)

/-- The exact subset-sum criterion: after splitting the available elements
into two disjoint parts, the upward and downward deviation subset sums have
no common value except zero. -/
def HasTrivialDeviationIntersections (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ A₁ A₂ : Finset ℕ,
    A₁ ⊆ A.erase a → A₂ ⊆ A.erase a → Disjoint A₁ A₂ →
      upperDeviationSums a A₁ ∩ lowerDeviationSums a A₂ = {0}

theorem isNonaveraging_iff_trivialDeviationIntersections (A : Finset ℕ) :
    IsNonaveraging A ↔ HasTrivialDeviationIntersections A := by
  constructor
  · intro hA a ha A₁ A₂ hA₁ hA₂ hdisj
    ext z
    constructor
    · intro hz
      simp only [mem_inter] at hz
      rcases (mem_subsetSums.mp hz.1) with ⟨B₁, hB₁, hsum₁⟩
      rcases (mem_subsetSums.mp hz.2) with ⟨B₂, hB₂, hsum₂⟩
      simp only [mem_singleton]
      by_contra hz0
      have hB₁ne : B₁.Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro h
        subst B₁
        simp at hsum₁
        exact hz0 hsum₁.symm
      have hB₂ne : B₂.Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro h
        subst B₂
        simp at hsum₂
        exact hz0 hsum₂.symm
      have hBdisj : Disjoint B₁ B₂ := hdisj.mono hB₁ hB₂
      have hBsub : B₁ ∪ B₂ ⊆ A.erase a := by
        intro x hx
        rcases mem_union.mp hx with hx | hx
        · exact hA₁ (hB₁ hx)
        · exact hA₂ (hB₂ hx)
      have hcard : 2 ≤ (B₁ ∪ B₂).card := by
        rw [card_union_of_disjoint hBdisj]
        have hcard₁ : 0 < B₁.card := card_pos.mpr hB₁ne
        have hcard₂ : 0 < B₂.card := card_pos.mpr hB₂ne
        omega
      have hint :
          ∑ x ∈ B₁ ∪ B₂, (x : ℤ) =
            ((B₁ ∪ B₂).card : ℤ) * (a : ℤ) := by
        rw [sum_union hBdisj, card_union_of_disjoint hBdisj, Nat.cast_add]
        simp only [sum_sub_distrib, sum_const, nsmul_eq_mul] at hsum₁
        simp only [sum_sub_distrib, sum_const, nsmul_eq_mul] at hsum₂
        linarith
      have hnat :
          (B₁ ∪ B₂).card * a = (B₁ ∪ B₂).sum id := by
        apply Nat.cast_injective (R := ℤ)
        push_cast
        simpa using hint.symm
      exact (hA a ha (B₁ ∪ B₂) hBsub hcard) hnat
    · intro hz
      have hz0 : z = 0 := by simpa using hz
      subst z
      exact mem_inter.mpr ⟨zero_mem_subsetSums _ _, zero_mem_subsetSums _ _⟩
  · intro hcrit a ha S hS hcard havg
    let A₁ := S.filter fun x ↦ a < x
    let A₂ := S.filter fun x ↦ x < a
    have hA₁sub : A₁ ⊆ A.erase a := by
      intro x hx
      exact hS (filter_subset _ _ hx)
    have hA₂sub : A₂ ⊆ A.erase a := by
      intro x hx
      exact hS (filter_subset _ _ hx)
    have hdisj : Disjoint A₁ A₂ := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx₁ hx₂
      have hx₁' : a < x := (mem_filter.mp hx₁).2
      have hx₂' : x < a := (mem_filter.mp hx₂).2
      omega
    have hunion : A₁ ∪ A₂ = S := by
      ext x
      constructor
      · intro hx
        rcases mem_union.mp hx with hx | hx
        · exact (mem_filter.mp hx).1
        · exact (mem_filter.mp hx).1
      · intro hx
        have hxa : x ≠ a := (mem_erase.mp (hS hx)).1
        rcases lt_or_gt_of_ne hxa with hlt | hgt
        · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hx, hlt⟩))
        · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hx, hgt⟩))
    have hA₁ne : A₁.Nonempty := by
      rw [nonempty_iff_ne_empty]
      intro hA₁empty
      have hxlt : ∀ x ∈ S, x < a := by
        intro x hx
        have hnot : ¬ a < x := by
          intro hax
          have : x ∈ A₁ := mem_filter.mpr ⟨hx, hax⟩
          rw [hA₁empty] at this
          simp at this
        have hxa : x ≠ a := (mem_erase.mp (hS hx)).1
        omega
      have hsum_le : S.sum (fun x ↦ x + 1) ≤ S.sum (fun _ ↦ a) := by
        exact sum_le_sum fun x hx ↦ Nat.add_one_le_iff.mpr (hxlt x hx)
      have hcardpos : 0 < S.card := by omega
      have : S.sum id + S.card ≤ S.card * a := by
        simpa [sum_add_distrib, nsmul_eq_mul] using hsum_le
      omega
    let z : ℤ := ∑ x ∈ A₁, ((x : ℤ) - (a : ℤ))
    have hzpos : 0 < z := by
      dsimp [z]
      exact sum_pos (fun x hx ↦ by
        have : a < x := (mem_filter.mp hx).2
        exact sub_pos.mpr (by exact_mod_cast this)) hA₁ne
    have hzero : ∑ x ∈ S, ((x : ℤ) - (a : ℤ)) = 0 := by
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
      have havg' : (S.card : ℤ) * (a : ℤ) = ∑ x ∈ S, (x : ℤ) := by
        rw [← Nat.cast_mul, havg]
        push_cast
        rfl
      linarith
    have hcommon :
        (∑ x ∈ A₁, ((x : ℤ) - (a : ℤ))) =
          ∑ x ∈ A₂, ((a : ℤ) - (x : ℤ)) := by
      rw [← hunion] at hzero
      rw [sum_union hdisj] at hzero
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul] at hzero ⊢
      linarith
    have hzmem₁ : z ∈ upperDeviationSums a A₁ := by
      apply mem_subsetSums.mpr
      exact ⟨A₁, Subset.rfl, rfl⟩
    have hzmem₂ : z ∈ lowerDeviationSums a A₂ := by
      apply mem_subsetSums.mpr
      exact ⟨A₂, Subset.rfl, hcommon.symm⟩
    have hinter := hcrit a ha A₁ A₂ hA₁sub hA₂sub hdisj
    have hzsingle : z ∈ ({0} : Finset ℤ) := by
      rw [← hinter]
      exact mem_inter.mpr ⟨hzmem₁, hzmem₂⟩
    have : z = 0 := by simpa using hzsingle
    omega

/-- A readable alias for the criterion theorem. -/
theorem subsetSumCriterion (A : Finset ℕ) :
    IsNonaveraging A ↔ HasTrivialDeviationIntersections A :=
  isNonaveraging_iff_trivialDeviationIntersections A

end

end Erdos186
