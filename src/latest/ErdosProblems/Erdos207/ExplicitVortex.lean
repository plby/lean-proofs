/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.Vortex

/-!
# Explicit finite vortices with prescribed sizes

For a fixed terminal set `X`, order the complement and take nested prefixes.
This gives a canonical vortex for every antitone size schedule, with exact
cardinalities whenever the requested sizes lie between `|X|` and the ambient
order.
-/

namespace Erdos207

open Finset

noncomputable section

/-- The first `r` vertices of the ordered complement of `X`. -/
def vortexComplementPrefix {n : ℕ} (X : Finset (Fin n)) (r : ℕ) :
    Finset (Fin n) :=
  (((univ \ X).sort (· ≤ ·)).take r).toFinset

lemma vortexComplementPrefix_subset_complement
    {n r : ℕ} (X : Finset (Fin n)) :
    vortexComplementPrefix X r ⊆ univ \ X := by
  intro x hx
  have hxTake : x ∈ ((univ \ X).sort (· ≤ ·)).take r := by
    simpa only [vortexComplementPrefix, List.mem_toFinset] using hx
  have hxSort := List.mem_of_mem_take hxTake
  simpa using hxSort

lemma vortexComplementPrefix_mono
    {n r s : ℕ} (X : Finset (Fin n)) (hrs : r ≤ s) :
    vortexComplementPrefix X r ⊆ vortexComplementPrefix X s := by
  intro x hx
  rw [vortexComplementPrefix, List.mem_toFinset] at hx ⊢
  exact List.take_subset_take_left ((univ \ X).sort (· ≤ ·)) hrs hx

lemma card_vortexComplementPrefix
    {n r : ℕ} (X : Finset (Fin n)) :
    (vortexComplementPrefix X r).card = min r (n - X.card) := by
  have hnodup : ((univ \ X).sort (· ≤ ·)).Nodup :=
    Finset.sort_nodup _ _
  rw [vortexComplementPrefix,
    List.toFinset_card_of_nodup (List.Pairwise.take hnodup),
    List.length_take]
  congr 1
  simpa only [Finset.length_sort, card_univ, Fintype.card_fin] using
    card_sdiff_of_subset (subset_univ X)

lemma disjoint_vortexComplementPrefix
    {n r : ℕ} (X : Finset (Fin n)) :
    Disjoint X (vortexComplementPrefix X r) := by
  rw [Finset.disjoint_left]
  intro x hxX hxPrefix
  exact (mem_sdiff.mp (vortexComplementPrefix_subset_complement X hxPrefix)).2 hxX

/-- The canonical vortex associated with an antitone integer size schedule.
Level zero is definitionally the ambient universe; later levels are `X`
plus an initial segment of its complement. -/
def vortexOfSizeSchedule {n ell : ℕ} (X : Finset (Fin n))
    (size : Fin (ell + 1) → ℕ) (hsize : Antitone size) :
    Vortex (Fin n) ell where
  U i := if i = 0 then univ
    else X ∪ vortexComplementPrefix X (size i - X.card)
  root := by simp
  antitone := by
    intro i j hij
    by_cases hi : i = 0
    · subst i
      simp
    have hj : j ≠ 0 := by
      intro hj
      subst j
      apply hi
      exact Fin.le_antisymm hij (Fin.zero_le i)
    simp only [hi, hj, ↓reduceIte]
    exact union_subset_union_right
      (vortexComplementPrefix_mono X
        (Nat.sub_le_sub_right (hsize hij) X.card))

@[simp] lemma vortexOfSizeSchedule_zero
    {n ell : ℕ} (X : Finset (Fin n))
    (size : Fin (ell + 1) → ℕ) (hsize : Antitone size) :
    (vortexOfSizeSchedule X size hsize).U 0 = univ := by
  simp [vortexOfSizeSchedule]

lemma vortexOfSizeSchedule_later
    {n ell : ℕ} (X : Finset (Fin n))
    (size : Fin (ell + 1) → ℕ) (hsize : Antitone size)
    (i : Fin (ell + 1)) (hi : i ≠ 0) :
    (vortexOfSizeSchedule X size hsize).U i =
      X ∪ vortexComplementPrefix X (size i - X.card) := by
  simp [vortexOfSizeSchedule, hi]

/-- Exact scheduled cardinality at every nonzero level. -/
lemma card_vortexOfSizeSchedule
    {n ell : ℕ} (X : Finset (Fin n))
    (size : Fin (ell + 1) → ℕ) (hsize : Antitone size)
    (hXsize : ∀ i, X.card ≤ size i) (hsizeN : ∀ i, size i ≤ n)
    (i : Fin (ell + 1)) (hi : i ≠ 0) :
    ((vortexOfSizeSchedule X size hsize).U i).card = size i := by
  rw [vortexOfSizeSchedule_later X size hsize i hi,
    card_union_of_disjoint (disjoint_vortexComplementPrefix X),
    card_vortexComplementPrefix]
  have hcomp : size i - X.card ≤ n - X.card :=
    Nat.sub_le_sub_right (hsizeN i) X.card
  rw [min_eq_left hcomp]
  have hx := hXsize i
  omega

/-- If the terminal requested size is exactly `|X|`, the terminal vortex set
is exactly `X`. -/
lemma vortexOfSizeSchedule_terminal
    {n ell : ℕ} (hell : 0 < ell) (X : Finset (Fin n))
    (size : Fin (ell + 1) → ℕ) (hsize : Antitone size)
    (hlast : size (Fin.last ell) = X.card) :
    (vortexOfSizeSchedule X size hsize).U (Fin.last ell) = X := by
  have hlast0 : (Fin.last ell : Fin (ell + 1)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_zero] at this
    omega
  rw [vortexOfSizeSchedule_later X size hsize (Fin.last ell) hlast0,
    hlast, Nat.sub_self, vortexComplementPrefix]
  simp

end

end Erdos207
