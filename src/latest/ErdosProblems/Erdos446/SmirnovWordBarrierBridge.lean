/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovWordMass
import ErdosProblems.Erdos446.SmirnovFirstCrossingWords

/-!
# Erdős Problem 446: equivalence of the two finite word models

The multinomial bridge and the first-crossing argument use two visibly
different formulas for a prefix count.  This file proves that they are the
same double count, and hence identifies their good and bad word finsets.
-/

namespace Erdos446

open Finset

theorem wordPrefix_eq_sum_wordOccupancy {k v : ℕ}
    (f : Fin k → Fin v) (h : ℕ) :
    wordPrefix f h =
      ∑ j ∈ (Finset.univ.filter fun j : Fin v ↦ j.val < h),
        wordOccupancy f j := by
  classical
  unfold wordPrefix wordOccupancy
  let s := (Finset.univ : Finset (Fin k)).filter fun i ↦ (f i).val < h
  let t := (Finset.univ : Finset (Fin v)).filter fun j ↦ j.val < h
  calc
    s.card = ∑ j ∈ t, #{i ∈ s | f i = j} :=
      Finset.card_eq_sum_card_fiberwise
        (f := f) (s := s) (t := t) (by
          intro i hi
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
    _ = ∑ j ∈ t, #{i ∈ (Finset.univ : Finset (Fin k)) | f i = j} := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun hi ↦ hi.2
      · intro hij
        refine ⟨?_, hij⟩
        have hjlt : j.val < h := (Finset.mem_filter.mp hj).2
        simpa [s, hij] using hjlt

theorem satisfiesWordBarrier_iff_mem_smirnovWords
    {k u v : ℕ} (f : Fin k → Fin v) :
    SatisfiesWordBarrier u f ↔ f ∈ smirnovWords k u v := by
  rw [SatisfiesWordBarrier, mem_smirnovWords]
  constructor <;> intro h n hn hnv
  · simpa [← wordPrefix_eq_sum_wordOccupancy f n] using h n hn hnv
  · simpa [← wordPrefix_eq_sum_wordOccupancy f n] using h n hn hnv

theorem barrierWords_eq_smirnovWords (k u v : ℕ) :
    barrierWords k u v = smirnovWords k u v := by
  classical
  ext f
  rw [mem_barrierWords, satisfiesWordBarrier_iff_mem_smirnovWords]

theorem card_barrierWords_eq_factorial_mul_mass (k u v : ℕ) :
    ((barrierWords k u v).card : ℝ) =
      (k.factorial : ℝ) * smirnovOccupancyMass k u v := by
  rw [barrierWords_eq_smirnovWords,
    card_smirnovWords_eq_factorial_mul_mass]

theorem smirnovProbability_eq_card_barrierWords_div {k u v : ℕ} :
    smirnovProbability k u v =
      ((barrierWords k u v).card : ℝ) / (v : ℝ) ^ k := by
  rw [barrierWords_eq_smirnovWords]
  exact smirnovProbability_eq_card_smirnovWords_div

theorem card_failedBarrierWords_eq_pow_sub (k u v : ℕ) :
    (failedBarrierWords k u v).card =
      v ^ k - (barrierWords k u v).card := by
  have h := card_barrierWords_add_failed k u v
  omega

theorem smirnovProbability_add_card_failedBarrierWords_div
    {k u v : ℕ} (hv : 0 < v) :
    smirnovProbability k u v +
        ((failedBarrierWords k u v).card : ℝ) / (v : ℝ) ^ k = 1 := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hpow : (v : ℝ) ^ k ≠ 0 := (pow_pos hvR k).ne'
  rw [smirnovProbability_eq_card_barrierWords_div, ← add_div]
  rw [← Nat.cast_add, card_barrierWords_add_failed]
  simp [hpow]

theorem smirnovProbability_eq_one_sub_card_failedBarrierWords_div
    {k u v : ℕ} (hv : 0 < v) :
    smirnovProbability k u v = 1 -
      ((failedBarrierWords k u v).card : ℝ) / (v : ℝ) ^ k := by
  linarith [smirnovProbability_add_card_failedBarrierWords_div
    (k := k) (u := u) hv]

theorem smirnovProbability_le_one_sub_of_le_card_failedBarrierWords
    {k u v : ℕ} (hv : 0 < v) {R : ℝ}
    (hR : R ≤ (failedBarrierWords k u v).card) :
    smirnovProbability k u v ≤ 1 - R / (v : ℝ) ^ k := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hpow : (0 : ℝ) < (v : ℝ) ^ k := pow_pos hvR k
  rw [smirnovProbability_eq_one_sub_card_failedBarrierWords_div hv]
  have hdiv := div_le_div_of_nonneg_right hR hpow.le
  linarith

end Erdos446
