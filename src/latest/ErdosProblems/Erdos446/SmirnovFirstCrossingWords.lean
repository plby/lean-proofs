/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovFiniteRatio
import Mathlib.Data.Nat.Find

/-!
# Erdős Problem 446: finite words and their first barrier crossing

This is the purely finite version of Ford's first-crossing decomposition.
A word `Fin k → Fin v` records the equal-cell containing each of the `k`
labelled uniform points.  Ties are ordered by the labels in `Fin k`.
-/

namespace Erdos446

open Finset

/-- Number of letters of a word in the first `h` slots. -/
def wordPrefix {k v : ℕ} (f : Fin k → Fin v) (h : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter fun i ↦ (f i).val < h).card

theorem wordPrefix_zero {k v : ℕ} (f : Fin k → Fin v) :
    wordPrefix f 0 = 0 := by
  simp [wordPrefix]

theorem wordPrefix_mono {k v : ℕ} (f : Fin k → Fin v) :
    Monotone (wordPrefix f) := by
  intro a b hab
  exact Finset.card_le_card (by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    omega)

theorem wordPrefix_eq_k_of_length_le {k v : ℕ} (f : Fin k → Fin v)
    {h : ℕ} (hvh : v ≤ h) :
    wordPrefix f h = k := by
  rw [wordPrefix, Finset.filter_eq_self.2]
  · simp
  · intro i _
    exact (f i).isLt.trans_le hvh

/-- The strict affine barrier on labelled finite words. -/
def SatisfiesWordBarrier {k v : ℕ} (u : ℕ) (f : Fin k → Fin v) : Prop :=
  ∀ h : ℕ, 1 ≤ h → h ≤ v → wordPrefix f h < u + h

noncomputable def barrierWords (k u v : ℕ) : Finset (Fin k → Fin v) := by
  classical
  exact Finset.univ.filter (SatisfiesWordBarrier u)

noncomputable def failedBarrierWords (k u v : ℕ) : Finset (Fin k → Fin v) := by
  classical
  exact Finset.univ.filter fun f ↦ ¬ SatisfiesWordBarrier u f

theorem mem_barrierWords {k u v : ℕ} {f : Fin k → Fin v} :
    f ∈ barrierWords k u v ↔ SatisfiesWordBarrier u f := by
  classical
  simp [barrierWords]

theorem mem_failedBarrierWords {k u v : ℕ} {f : Fin k → Fin v} :
    f ∈ failedBarrierWords k u v ↔ ¬ SatisfiesWordBarrier u f := by
  classical
  simp [failedBarrierWords]

theorem card_barrierWords_add_failed (k u v : ℕ) :
    (barrierWords k u v).card + (failedBarrierWords k u v).card = v ^ k := by
  classical
  rw [barrierWords, failedBarrierWords,
    Finset.card_filter_add_card_filter_not]
  simp

private def firstFailureExists {k v : ℕ} (u : ℕ) (f : Fin k → Fin v) :
    ∃ h : ℕ,
      (1 ≤ h ∧ h ≤ v ∧ u + h ≤ wordPrefix f h) ∨ h = v + 1 :=
  ⟨v + 1, Or.inr rfl⟩

/-- First slot at whose right endpoint the word crosses the barrier.  The
sentinel `v+1` makes this a total definition on good words as well. -/
def firstFailedSlot {k v : ℕ} (u : ℕ) (f : Fin k → Fin v) : ℕ :=
  Nat.find (firstFailureExists u f)

theorem exists_failedSlot_of_not_wordBarrier
    {k u v : ℕ} {f : Fin k → Fin v}
    (hbad : ¬ SatisfiesWordBarrier u f) :
    ∃ h, 1 ≤ h ∧ h ≤ v ∧ u + h ≤ wordPrefix f h := by
  simp only [SatisfiesWordBarrier] at hbad
  push_neg at hbad
  exact hbad

theorem firstFailedSlot_spec
    {k u v : ℕ} {f : Fin k → Fin v}
    (hbad : ¬ SatisfiesWordBarrier u f) :
    1 ≤ firstFailedSlot u f ∧ firstFailedSlot u f ≤ v ∧
      u + firstFailedSlot u f ≤ wordPrefix f (firstFailedSlot u f) := by
  obtain ⟨h, hh, hvh, hfail⟩ := exists_failedSlot_of_not_wordBarrier hbad
  have hle : firstFailedSlot u f ≤ h :=
    Nat.find_min' (firstFailureExists u f) (Or.inl ⟨hh, hvh, hfail⟩)
  have hle' : Nat.find (firstFailureExists u f) ≤ h := by
    simpa [firstFailedSlot] using hle
  have hspec := Nat.find_spec (firstFailureExists u f)
  unfold firstFailedSlot
  rcases hspec with hspec | heq
  · exact hspec
  · exfalso
    omega

theorem wordBarrier_before_firstFailedSlot
    {k u v : ℕ} {f : Fin k → Fin v}
    (hbad : ¬ SatisfiesWordBarrier u f)
    {h : ℕ} (hh : 1 ≤ h) (hlt : h < firstFailedSlot u f) :
    wordPrefix f h < u + h := by
  have hfirst := (firstFailedSlot_spec hbad).2.1
  have hlt' : h < Nat.find (firstFailureExists u f) := by
    simpa [firstFailedSlot] using hlt
  have hmin := Nat.find_min (firstFailureExists u f) hlt'
  by_contra hnot
  apply hmin
  exact Or.inl ⟨hh, by omega, by omega⟩

/-- Labels in one specified slot. -/
def wordSlotLabels {k v : ℕ} (f : Fin k → Fin v) (s : ℕ) :
    Finset (Fin k) :=
  Finset.univ.filter fun i ↦ (f i).val = s

theorem wordPrefix_succ_eq_add_slot {k v : ℕ} (f : Fin k → Fin v)
    (s : ℕ) :
    wordPrefix f (s + 1) = wordPrefix f s + (wordSlotLabels f s).card := by
  rw [wordPrefix, wordPrefix, wordSlotLabels, ← Finset.card_union_of_disjoint]
  · congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      obtain hi | hi := lt_or_eq_of_le (Nat.lt_succ_iff.mp (by simpa using hi))
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (hi | hi)
      · exact Nat.lt_succ_of_lt hi
      · simpa [hi]
  · rw [Finset.disjoint_left]
    intro i hi hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    rw [hj] at hi
    exact (Nat.lt_irrefl _ hi)

theorem crossingDeficit_pos
    {k u v : ℕ} {f : Fin k → Fin v}
    (hbad : ¬ SatisfiesWordBarrier u f) :
    0 < u + firstFailedSlot u f -
      wordPrefix f (firstFailedSlot u f - 1) := by
  have hspec := firstFailedSlot_spec hbad
  by_cases hone : firstFailedSlot u f = 1
  · rw [hone]
    simp [wordPrefix_zero]
  · have hprev := wordBarrier_before_firstFailedSlot hbad
      (h := firstFailedSlot u f - 1) (by omega) (by omega)
    omega

theorem crossingDeficit_le_slotCard
    {k u v : ℕ} {f : Fin k → Fin v}
    (hbad : ¬ SatisfiesWordBarrier u f) :
    u + firstFailedSlot u f -
        wordPrefix f (firstFailedSlot u f - 1) ≤
      (wordSlotLabels f (firstFailedSlot u f - 1)).card := by
  have hspec := firstFailedSlot_spec hbad
  have hsucc := wordPrefix_succ_eq_add_slot f
    (firstFailedSlot u f - 1)
  have heq : firstFailedSlot u f - 1 + 1 = firstFailedSlot u f := by
    omega
  rw [heq] at hsucc
  omega

/-- A bad word together with the proof needed to define its crossing label. -/
abbrev FailedWord (k u v : ℕ) :=
  {f : Fin k → Fin v // ¬ SatisfiesWordBarrier u f}

/-- Label of the point which first crosses the affine barrier, using the
ambient label order to resolve ties inside a slot. -/
noncomputable def firstCrossingLabel {k u v : ℕ}
    (F : FailedWord k u v) : Fin k := by
  let d := u + firstFailedSlot u F.1 -
    wordPrefix F.1 (firstFailedSlot u F.1 - 1)
  let S := wordSlotLabels F.1 (firstFailedSlot u F.1 - 1)
  have hd : 0 < d := by
    simpa [d] using crossingDeficit_pos F.2
  have hdS : d ≤ S.card := by
    simpa [d, S] using crossingDeficit_le_slotCard F.2
  exact (S.orderIsoOfFin rfl ⟨d - 1, by omega⟩).1

theorem card_filter_le_orderIso {k : ℕ} (S : Finset (Fin k))
    (j : Fin S.card) :
    (S.filter fun x ↦ x ≤ (S.orderIsoOfFin rfl j).1).card = j.val + 1 := by
  let e := S.orderIsoOfFin rfl
  let T := S.filter fun x ↦ x ≤ (e j).1
  have hcard : T.card = (Finset.Iic j).card := by
    apply Finset.card_bij (fun x hx ↦ e.symm ⟨x, (Finset.mem_filter.mp hx).1⟩)
    · intro x hx
      rw [Finset.mem_Iic]
      apply e.le_iff_le.mp
      rw [e.apply_symm_apply]
      exact (Finset.mem_filter.mp hx).2
    · intro x hx y hy hxy
      have hsub : (⟨x, (Finset.mem_filter.mp hx).1⟩ : S) =
          ⟨y, (Finset.mem_filter.mp hy).1⟩ := e.symm.injective hxy
      exact congrArg Subtype.val hsub
    · intro i hi
      refine ⟨(e i).1, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨(e i).2, by
          apply e.le_iff_le.mpr
          simpa using (Finset.mem_Iic.mp hi)⟩
      · exact e.symm_apply_apply i
  rw [hcard, Fin.card_Iic]

theorem firstCrossingLabel_mem_slot {k u v : ℕ}
    (F : FailedWord k u v) :
    firstCrossingLabel F ∈
      wordSlotLabels F.1 (firstFailedSlot u F.1 - 1) := by
  classical
  unfold firstCrossingLabel
  dsimp only
  exact (wordSlotLabels F.1 (firstFailedSlot u F.1 - 1)).orderIsoOfFin
    rfl ⟨u + firstFailedSlot u F.1 -
      wordPrefix F.1 (firstFailedSlot u F.1 - 1) - 1, by
        have h := crossingDeficit_le_slotCard F.2
        have hp := crossingDeficit_pos F.2
        omega⟩ |>.2

theorem card_slotLabels_le_firstCrossingLabel {k u v : ℕ}
    (F : FailedWord k u v) :
    ((wordSlotLabels F.1 (firstFailedSlot u F.1 - 1)).filter
      fun i ↦ i ≤ firstCrossingLabel F).card =
        u + firstFailedSlot u F.1 -
          wordPrefix F.1 (firstFailedSlot u F.1 - 1) := by
  classical
  let d := u + firstFailedSlot u F.1 -
    wordPrefix F.1 (firstFailedSlot u F.1 - 1)
  let S := wordSlotLabels F.1 (firstFailedSlot u F.1 - 1)
  have hd : 0 < d := by simpa [d] using crossingDeficit_pos F.2
  have hdS : d ≤ S.card := by
    simpa [d, S] using crossingDeficit_le_slotCard F.2
  have h := card_filter_le_orderIso S ⟨d - 1, by omega⟩
  have hdEq : d - 1 + 1 = d := by omega
  rw [hdEq] at h
  have hlabel : firstCrossingLabel F =
      (S.orderIsoOfFin rfl ⟨d - 1, by omega⟩).1 := by
    rfl
  rw [hlabel]
  simpa [d, S] using h

end Erdos446
