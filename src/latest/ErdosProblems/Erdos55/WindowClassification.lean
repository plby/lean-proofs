/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.SparseWindows

/-!
# Classifying summands from the selected windows

The sparseness of the selected weak scales implies that, below the current
target endpoint, a blue element lies either in the current window or in the
single prefix which contains every earlier window.  We then split any blue
subset accordingly and map its two partial sums into `blueHuePossible`.
-/

namespace Erdos55

open scoped BigOperators

theorem mem_blueWindow_iff {A : Set ℕ} (hA : A.Infinite) {j a : ℕ} :
    a ∈ blueWindow A j ↔ a ∈ A ∧ 2 ^ j < a ∧ a ≤ j * 2 ^ j := by
  rw [blueWindow, Finset.mem_sdiff, mem_rankPrefix_iff hA,
    mem_rankPrefix_iff hA]
  constructor
  · rintro ⟨⟨haA, haU⟩, haL⟩
    refine ⟨haA, ?_, haU⟩
    by_contra hnot
    exact haL ⟨haA, Nat.le_of_not_gt hnot⟩
  · rintro ⟨haA, haL, haU⟩
    exact ⟨⟨haA, haU⟩, fun h ↦ (not_lt_of_ge h.2) haL⟩

theorem mem_blueHueWindow_iff {A : Set ℕ} (hA : A.Infinite)
    {h s j a : ℕ} :
    a ∈ blueHueWindow A h s j ↔
      a ∈ A ∧ hueIn A h a = s ∧ 2 ^ j < a ∧ a ≤ j * 2 ^ j := by
  rw [blueHueWindow, Finset.mem_sdiff, mem_rankHuePrefix_iff hA,
    mem_rankHuePrefix_iff hA]
  constructor
  · rintro ⟨⟨haA, haU, hahue⟩, haL⟩
    refine ⟨haA, hahue, ?_, haU⟩
    by_contra hnot
    exact haL ⟨haA, Nat.le_of_not_gt hnot, hahue⟩
  · rintro ⟨haA, hahue, haL, haU⟩
    exact ⟨⟨haA, haU, hahue⟩, fun h ↦ (not_lt_of_ge h.2.1) haL⟩

theorem selectedBlue_index_le {A : Set ℕ} (hA : A.Infinite)
    {J : ℕ → ℕ} (hJ : StrictMono J) {n a : ℕ}
    (hgap : J n * 2 ^ J n < J (n + 1))
    (haU : a ≤ J n * 2 ^ J n) (ha : selectedBlue A J a) :
    ∃ k ≤ n, a ∈ blueWindow A (J k) := by
  obtain ⟨k, hak⟩ := ha
  refine ⟨k, ?_, hak⟩
  by_contra hkn
  have hnk : n + 1 ≤ k := by omega
  have hJle : J (n + 1) ≤ J k := hJ.monotone hnk
  have hpow : J k < 2 ^ J k := (J k).lt_two_pow_self
  have halower : 2 ^ J k < a := (mem_blueWindow_iff hA).mp hak |>.2.1
  omega

theorem selectedBlue_mem_earlier_or_current {A : Set ℕ} (hA : A.Infinite)
    {h s : ℕ} {J : ℕ → ℕ} (hJ : StrictMono J) {n a : ℕ}
    (hgap : J n * 2 ^ J n < J (n + 1))
    (haA : a ∈ A) (hahue : hueIn A h a = s)
    (haU : a ≤ J n * 2 ^ J n) (ha : selectedBlue A J a) :
    a ∈ earlierHuePrefix A h s J n ∨ a ∈ blueHueWindow A h s (J n) := by
  obtain ⟨k, hkn, hak⟩ := selectedBlue_index_le hA hJ hgap haU ha
  rcases hkn.eq_or_lt with rfl | hkn
  · exact Or.inr ((mem_blueHueWindow_iff hA).mpr
      ⟨haA, hahue, (mem_blueWindow_iff hA).mp hak |>.2.1, haU⟩)
  · cases n with
    | zero => omega
    | succ n =>
        apply Or.inl
        have hkn' : k ≤ n := by omega
        have hscale : J k * 2 ^ J k ≤ J n * 2 ^ J n :=
          scaleProduct_mono (hJ.monotone hkn')
        have haUpper : a ≤ J n * 2 ^ J n :=
          ((mem_blueWindow_iff hA).mp hak).2.2.trans hscale
        simpa [earlierHuePrefix] using
          (mem_rankHuePrefix_iff hA).mpr ⟨haA, haUpper, hahue⟩

theorem sparseWeakSequence_window_gap {P : ℕ → Prop}
    (hunbounded : ∀ b, ∃ j, b < j ∧ P j) (A : Set ℕ) (h n : ℕ) :
    sparseWeakSequence hunbounded A h n *
        2 ^ sparseWeakSequence hunbounded A h n <
      sparseWeakSequence hunbounded A h (n + 1) := by
  exact (le_max_left _ _).trans_lt
    (sparseWeakSequence_succ_gt hunbounded A h n)

theorem sum_mem_currentBlueOptions {A : Set ℕ} (hA : A.Infinite)
    {h s j : ℕ} {T : Finset ℕ}
    (hT : T ⊆ blueHueWindow A h s j)
    (hsum : ∑ a ∈ T, a ≤ j * 2 ^ j) :
    (∑ a ∈ T, a) ∈ currentBlueOptions A h s j := by
  classical
  by_cases hz : (∑ a ∈ T, a) = 0
  · simpa [currentBlueOptions, hz]
  · apply Finset.mem_insert_of_mem
    unfold blueHueRepresented
    apply Finset.mem_filter.mpr
    refine ⟨?_, ⟨Nat.one_le_iff_ne_zero.mpr hz, hsum⟩⟩
    apply mem_subsetSumValues.mpr
    exact ⟨T, hT, rfl⟩

theorem finset_eq_inter_union_sdiff (T E : Finset ℕ) :
    T = T ∩ E ∪ (T \ E) := by
  ext a
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem sum_mem_blueHuePossible {A : Set ℕ} (hA : A.Infinite)
    {h s : ℕ} {J : ℕ → ℕ} (hJ : StrictMono J) {n : ℕ}
    (hgap : J n * 2 ^ J n < J (n + 1)) {T : Finset ℕ}
    (hTA : ∀ a ∈ T, a ∈ A)
    (hThue : ∀ a ∈ T, hueIn A h a = s)
    (hTblue : ∀ a ∈ T, selectedBlue A J a)
    (hsum : ∑ a ∈ T, a ≤ J n * 2 ^ J n) :
    (∑ a ∈ T, a) ∈ blueHuePossible A h s J n := by
  classical
  let E := earlierHuePrefix A h s J n
  let B := blueHueWindow A h s (J n)
  let TE := T ∩ E
  let TB := T \ E
  have ha_le_sum : ∀ a ∈ T, a ≤ ∑ x ∈ T, x := by
    intro a ha
    exact Finset.single_le_sum (s := T) (f := fun x : ℕ ↦ x)
      (fun x _ ↦ Nat.zero_le x) ha
  have hclass : T ⊆ E ∪ B := by
    intro a ha
    rcases selectedBlue_mem_earlier_or_current hA hJ hgap
        (hTA a ha) (hThue a ha) ((ha_le_sum a ha).trans hsum) (hTblue a ha) with
      haE | haB
    · exact Finset.mem_union_left _ haE
    · exact Finset.mem_union_right _ haB
  have hTE : TE ⊆ E := Finset.inter_subset_right
  have hTB : TB ⊆ B := by
    intro a ha
    have ha' := Finset.mem_sdiff.mp ha
    rcases Finset.mem_union.mp (hclass ha'.1) with haE | haB
    · exact (ha'.2 haE).elim
    · exact haB
  have hdisj : Disjoint TE TB := by
    rw [Finset.disjoint_left]
    intro a haTE haTB
    exact (Finset.mem_sdiff.mp haTB).2 (Finset.mem_inter.mp haTE).2
  have hunion : T = TE ∪ TB := by
    simpa [TE, TB, E] using finset_eq_inter_union_sdiff T E
  have hsumSplit : (∑ a ∈ T, a) =
      (∑ a ∈ TE, a) + ∑ a ∈ TB, a := by
    rw [hunion, Finset.sum_union hdisj]
  apply Finset.mem_image₂.mpr
  refine ⟨∑ a ∈ TE, a, ?_, ∑ a ∈ TB, a, ?_, hsumSplit.symm⟩
  · exact mem_subsetSumValues.mpr ⟨TE, hTE, rfl⟩
  · apply sum_mem_currentBlueOptions hA hTB
    have hpart : ∑ a ∈ TB, a ≤ ∑ a ∈ T, a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      intro a _ _
      exact Nat.zero_le a
    exact hpart.trans hsum

theorem sum_mem_bluePossible {A : Set ℕ} (hA : A.Infinite)
    {h : ℕ} (hh : 0 < h) {J : ℕ → ℕ} (hJ : StrictMono J) {n : ℕ}
    (hgap : J n * 2 ^ J n < J (n + 1)) {T : Finset ℕ}
    (hTA : ∀ a ∈ T, a ∈ A)
    (hThue : ∃ s < h, ∀ a ∈ T, hueIn A h a = s)
    (hTblue : ∀ a ∈ T, selectedBlue A J a)
    (hsum : ∑ a ∈ T, a ≤ J n * 2 ^ J n) :
    (∑ a ∈ T, a) ∈ bluePossible A h J n := by
  obtain ⟨s, hs, hTs⟩ := hThue
  unfold bluePossible
  apply Finset.mem_biUnion.mpr
  exact ⟨s, Finset.mem_range.mpr hs,
    sum_mem_blueHuePossible hA hJ hgap hTA hTs hTblue hsum⟩

end Erdos55
