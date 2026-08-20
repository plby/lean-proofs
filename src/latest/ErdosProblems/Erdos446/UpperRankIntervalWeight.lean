/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperCrowdingMass

/-!
# Erdős Problem 446: exponential weights of rank intervals

This file connects the two ways in which the upper-bound argument records a
prefix of an occupancy vector.  `blockPrefixWeight c q` sums the dyadic cell
weights through cell `q`, whereas `occupancyRankIntervalWeight c a b` sums
the same weights over the objects having ranks in `[a,b)`.  The bridge below
allows Ford's linear rank cutoff to be inserted into the discrete crowding
decomposition without changing coordinates.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- Dyadic cell weight carried by the objects whose ranks lie in `[a,b)`.
Ranks are zero based, as in `occupancyRankInterval`. -/
def occupancyRankIntervalWeight {v : ℕ} (c : Fin v → ℕ)
    (a b : ℕ) : ℕ :=
  ∑ i : Fin v, occupancyRankInterval c a b i * 2 ^ i.val

theorem occupancyRankInterval_zero_left {v : ℕ} (c : Fin v → ℕ)
    (b : ℕ) (i : Fin v) :
    occupancyRankInterval c 0 b i = occupancyTake c b i := by
  simp [occupancyRankInterval, occupancyTake]

/-- If cell `q` ends at rank `l`, the cell-prefix weight is exactly the
weight of the first `l` objects. -/
theorem blockPrefixWeight_eq_occupancyRankIntervalWeight
    {v : ℕ} (c : Fin v → ℕ) {q l : ℕ}
    (hq : q ≤ v) (hql : occupancyPrefix c q = l) :
    blockPrefixWeight c q = occupancyRankIntervalWeight c 0 l := by
  classical
  rw [blockPrefixWeight, occupancyRankIntervalWeight]
  have hpointInside (i : Fin v) (hiq : i.val < q) :
      occupancyRankInterval c 0 l i = c i := by
    have hi1q : i.val + 1 ≤ q := by omega
    have hpref : occupancyPrefix c (i.val + 1) ≤ l := by
      rw [← hql]
      exact occupancyPrefix_mono c hi1q
    have hsucc : occupancyPrefix c (i.val + 1) =
        occupancyPrefix c i.val + c i := by
      simpa only [Fin.eta] using occupancyPrefix_succ c i.isLt
    have hci : c i ≤ l - occupancyPrefix c i.val := by omega
    rw [occupancyRankInterval_zero_left, occupancyTake, min_eq_left hci]
  have hpointOutside (i : Fin v) (hqi : q ≤ i.val) :
      occupancyRankInterval c 0 l i = 0 := by
    have hpref : l ≤ occupancyPrefix c i.val := by
      rw [← hql]
      exact occupancyPrefix_mono c hqi
    rw [occupancyRankInterval_zero_left, occupancyTake]
    simp [Nat.sub_eq_zero_of_le hpref]
  calc
    (∑ i ∈ Finset.range q, extendComposition c i * 2 ^ i) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin v ↦ i.val < q),
          occupancyRankInterval c 0 l i * 2 ^ i.val := by
      apply Finset.sum_bij (fun i hi ↦
        ⟨i, (Finset.mem_range.mp hi).trans_le hq⟩)
      · intro i hi
        simp [Finset.mem_range.mp hi]
      · intro i₁ hi₁ i₂ hi₂ heq
        simpa using congrArg Fin.val heq
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        refine ⟨i.val, Finset.mem_range.mpr hi, Fin.ext rfl⟩
      · intro i hi
        rw [extendComposition]
        rw [dif_pos ((Finset.mem_range.mp hi).trans_le hq)]
        simp only
        rw [hpointInside _ (Finset.mem_range.mp hi)]
    _ = ∑ i : Fin v, occupancyRankInterval c 0 l i * 2 ^ i.val := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hnot
      simp only [Finset.mem_univ] at hi
      have hqi : q ≤ i.val := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
          not_lt] using hnot
      rw [hpointOutside i hqi, zero_mul]

/-- Rank-interval weights split additively at an intermediate rank. -/
theorem occupancyRankIntervalWeight_add
    {v : ℕ} (c : Fin v → ℕ) {a b d : ℕ}
    (hab : a ≤ b) (hbd : b ≤ d) :
    occupancyRankIntervalWeight c a b +
        occupancyRankIntervalWeight c b d =
      occupancyRankIntervalWeight c a d := by
  rw [occupancyRankIntervalWeight, occupancyRankIntervalWeight,
    occupancyRankIntervalWeight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hac : occupancyTake c a i ≤ occupancyTake c b i :=
    occupancyTake_mono c hab i
  have hbc : occupancyTake c b i ≤ occupancyTake c d i :=
    occupancyTake_mono c hbd i
  dsimp [occupancyRankInterval]
  have hsub : occupancyTake c b i - occupancyTake c a i +
      (occupancyTake c d i - occupancyTake c b i) =
        occupancyTake c d i - occupancyTake c a i := by omega
  rw [← add_mul, hsub]

/-- An interval ending before the prefix through cell `s` has at most its
cardinality times the endpoint weight `2^s`. -/
theorem occupancyRankIntervalWeight_le_card_mul_pow
    {v : ℕ} (c : Fin v → ℕ) {a b s : ℕ}
    (hab : a ≤ b) (hs : s ≤ v)
    (hb : b ≤ occupancyPrefix c s) :
    occupancyRankIntervalWeight c a b ≤ (b - a) * 2 ^ s := by
  have hprefTotal : occupancyPrefix c s ≤ ∑ i, c i := by
    rw [← occupancyPrefix_at_length]
    exact occupancyPrefix_mono c hs
  have hbTotal : b ≤ ∑ i, c i := hb.trans hprefTotal
  calc
    occupancyRankIntervalWeight c a b ≤
        ∑ i : Fin v, occupancyRankInterval c a b i * 2 ^ s := by
      rw [occupancyRankIntervalWeight]
      apply Finset.sum_le_sum
      intro i hi
      by_cases his : i.val < s
      · exact Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by omega) (by omega))
      · have hsi : s ≤ i.val := by omega
        have hbPrefix : b ≤ occupancyPrefix c i.val :=
          hb.trans (occupancyPrefix_mono c hsi)
        have htakeB : occupancyTake c b i = 0 := by
          simp [occupancyTake, Nat.sub_eq_zero_of_le hbPrefix]
        have htakeA : occupancyTake c a i = 0 := by
          have haPrefix : a ≤ occupancyPrefix c i.val :=
            hab.trans hbPrefix
          simp [occupancyTake, Nat.sub_eq_zero_of_le haPrefix]
        simp [occupancyRankInterval, htakeA, htakeB]
    _ = (∑ i : Fin v, occupancyRankInterval c a b i) * 2 ^ s := by
      rw [Finset.sum_mul]
    _ = (b - a) * 2 ^ s := by
      rw [sum_occupancyRankInterval (c := c) (total := ∑ i, c i)
        rfl hab hbTotal]

/-- Sharper endpoint version: for a nonempty cell prefix, ranks ending before
`C(s)` have cell weight at most `2^(s-1)`. -/
theorem occupancyRankIntervalWeight_le_card_mul_prevPow
    {v : ℕ} (c : Fin v → ℕ) {a b s : ℕ}
    (hab : a ≤ b) (hs : s ≤ v) (hs0 : 0 < s)
    (hb : b ≤ occupancyPrefix c s) :
    occupancyRankIntervalWeight c a b ≤ (b - a) * 2 ^ (s - 1) := by
  have hprefTotal : occupancyPrefix c s ≤ ∑ i, c i := by
    rw [← occupancyPrefix_at_length]
    exact occupancyPrefix_mono c hs
  have hbTotal : b ≤ ∑ i, c i := hb.trans hprefTotal
  calc
    occupancyRankIntervalWeight c a b ≤
        ∑ i : Fin v, occupancyRankInterval c a b i * 2 ^ (s - 1) := by
      rw [occupancyRankIntervalWeight]
      apply Finset.sum_le_sum
      intro i hi
      by_cases his : i.val < s
      · exact Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by omega) (by omega))
      · have hsi : s ≤ i.val := by omega
        have hbPrefix : b ≤ occupancyPrefix c i.val :=
          hb.trans (occupancyPrefix_mono c hsi)
        have htakeB : occupancyTake c b i = 0 := by
          simp [occupancyTake, Nat.sub_eq_zero_of_le hbPrefix]
        have htakeA : occupancyTake c a i = 0 := by
          have haPrefix : a ≤ occupancyPrefix c i.val :=
            hab.trans hbPrefix
          simp [occupancyTake, Nat.sub_eq_zero_of_le haPrefix]
        simp [occupancyRankInterval, htakeA, htakeB]
    _ = (∑ i : Fin v, occupancyRankInterval c a b i) * 2 ^ (s - 1) := by
      rw [Finset.sum_mul]
    _ = (b - a) * 2 ^ (s - 1) := by
      rw [sum_occupancyRankInterval (c := c) (total := ∑ i, c i)
        rfl hab hbTotal]

end Erdos446
