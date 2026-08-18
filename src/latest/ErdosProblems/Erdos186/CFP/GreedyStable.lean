/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.GreedyProcess
import ErdosProblems.Erdos186.CFP.Preprocessing

/-!
# Stable source thresholds for the CFP greedy process

This module connects the concrete finite thresholds from the proof of CFP
Theorem 1.5 to the checked `HApproximation` and weak-stability estimates.
The output is the uniform consecutive-threshold ratio required by the
abstract residence-time argument in `GreedyProcess`.
-/

namespace Erdos186.CFP.Greedy

open Erdos186.CFP

/-- A run staying in one consecutive pair of concrete source thresholds
has the expected dyadic length bound.  The fold used here is `2^(h+1)`,
because the strict upper endpoint is `t_(h+1)`. -/
theorem greedy_threshold_run_length_le_of_positiveDyadicThreshold
    {A : Finset ℤ} {p r h deletionBudget ratio : ℕ}
    (hr : 0 < r) (hsteps : p + r ≤ A.card)
    (hbudget : p + r ≤ deletionBudget)
    (hratio : positiveDyadicThreshold A deletionBudget (h + 1) ≤
      ratio * positiveDyadicThreshold A deletionBudget h)
    (hbin : ∀ i < r,
      positiveDyadicThreshold A deletionBudget h ≤
          (sums A (p + i)).card ∧
        (sums A (p + i)).card <
          positiveDyadicThreshold A deletionBudget (h + 1)) :
    r ≤ 4 * ratio * 2 ^ (h + 1) := by
  apply greedy_threshold_run_length_le_of_ratio hr hsteps
    (positiveDyadicThreshold_pos A deletionBudget h) hratio
  · intro i hi
    exact (hbin i hi).1
  · intro i hi
    exact (hbin i hi).2
  · intro i hi
    apply dyadicHighFold_of_card_sums_lt_positiveThreshold
      (j := p + i) (deletionBudget := deletionBudget) (h := h + 1)
    · omega
    · omega
    · exact (hbin i hi).2

/-- The source's consecutive-threshold comparison.  The approximation of
the ambient anchored color class controls doubling, while Lemma 2.31
compares it with the minimizing accessible subset.  The `+1` in
`positiveDyadicThreshold` absorbs both occurrences of integer division by
two. -/
theorem positiveDyadicThreshold_succ_le_of_approximations
    {A : Finset ℤ} {deletionBudget D n scaleNum scaleDen h dA : ℕ}
    (hzeroA : 0 ∉ A)
    (hstable : Stability.WeaklyStableMinimalFor
      (insert 0 A) deletionBudget D n)
    (hinterval : ∀ z ∈ insert 0 A, 0 ≤ z ∧ z < (n : ℤ))
    (WA : HDimension.HApproximation
      (insert 0 A) (2 ^ h) dA scaleNum scaleDen)
    (hdA : 0 < dA) (hdAD : dA ≤ D) (hfoldn : 2 ^ h ≤ n)
    (haccessible : ∀ B : Finset ℤ, B ⊆ A →
      A.card ≤ B.card + deletionBudget →
      ∃ dB : ℕ, 0 < dB ∧ dB ≤ D ∧
        ∃ WB : HDimension.HApproximation
            (insert 0 B) (2 ^ h) dB scaleNum scaleDen,
          (2 * scaleDen) ^ dB * (2 ^ h + 1) ^ (dB - 1) <
            (scaleNum * 2 ^ h) ^ dB) :
    positiveDyadicThreshold A deletionBudget (h + 1) ≤
      (2 * (6 * scaleDen) ^ D * (4 * (4 * scaleDen) ^ D) + 1) *
        positiveDyadicThreshold A deletionBudget h := by
  let fold := 2 ^ h
  let K := (6 * scaleDen) ^ D
  let C := 4 * (4 * scaleDen) ^ D
  obtain ⟨B, hBA, hBcard, hBmin⟩ :=
    exists_largeSubset_card_multifold_eq_minimum A deletionBudget fold
  obtain ⟨dB, hdB, hdBD, WB, hnumericB⟩ :=
    haccessible B hBA hBcard
  have hzeroB : 0 ∉ B := fun hzero ↦ hzeroA (hBA hzero)
  have hinsertBA : insert 0 B ⊆ insert 0 A :=
    Finset.insert_subset_insert 0 hBA
  have hinsertCard : (insert 0 A).card ≤
      (insert 0 B).card + deletionBudget := by
    rw [Finset.card_insert_of_notMem hzeroA,
      Finset.card_insert_of_notMem hzeroB]
    omega
  have hretains :
      3 * (GrowthLemmas.multifoldSumset fold (insert 0 A)).card <
        4 * (4 * scaleDen) ^ dB *
          (GrowthLemmas.multifoldSumset fold (insert 0 B)).card := by
    apply Preprocessing.HApproximation.three_mul_card_reference_multifoldSumset_lt
      hstable hinsertBA hinsertCard WB hdB hdBD
    · simpa only [fold] using hfoldn
    · exact hinterval
    · simpa only [fold] using hnumericB
  have hpowB : (4 * scaleDen) ^ dB ≤ (4 * scaleDen) ^ D := by
    exact Nat.pow_le_pow_right
      (Nat.mul_pos (by omega : 0 < 4) WB.scaleDen_pos) hdBD
  have hambient :
      (GrowthLemmas.multifoldSumset fold (insert 0 A)).card ≤
        C * (GrowthLemmas.multifoldSumset fold (insert 0 B)).card := by
    calc
      (GrowthLemmas.multifoldSumset fold (insert 0 A)).card ≤
          3 * (GrowthLemmas.multifoldSumset fold (insert 0 A)).card := by
        omega
      _ ≤ 4 * (4 * scaleDen) ^ dB *
          (GrowthLemmas.multifoldSumset fold (insert 0 B)).card :=
        hretains.le
      _ ≤ C * (GrowthLemmas.multifoldSumset fold (insert 0 B)).card := by
        dsimp only [C]
        gcongr
  have hpowA : (6 * scaleDen) ^ dA ≤ K := by
    dsimp only [K]
    exact Nat.pow_le_pow_right
      (Nat.mul_pos (by omega : 0 < 6) WA.scaleDen_pos) hdAD
  have hdouble :
      (GrowthLemmas.multifoldSumset (2 * fold) (insert 0 A)).card ≤
        K * (GrowthLemmas.multifoldSumset fold (insert 0 A)).card := by
    exact WA.card_two_mul_multifoldSumset_le.trans
      (Nat.mul_le_mul_right _ hpowA)
  have hnextMin :
      minimumMultifoldCardinality A deletionBudget (2 ^ (h + 1)) ≤
        K * C * minimumMultifoldCardinality A deletionBudget fold := by
    have hminimumA :
        minimumMultifoldCardinality A deletionBudget (2 ^ (h + 1)) ≤
          (GrowthLemmas.multifoldSumset (2 ^ (h + 1)) (insert 0 A)).card :=
      minimumMultifoldCardinality_le (B := A) (Finset.Subset.rfl) (by omega)
    calc
      minimumMultifoldCardinality A deletionBudget (2 ^ (h + 1)) ≤
          (GrowthLemmas.multifoldSumset (2 ^ (h + 1))
            (insert 0 A)).card := hminimumA
      _ = (GrowthLemmas.multifoldSumset (2 * fold)
            (insert 0 A)).card := by
        congr 2
        simp [fold, pow_succ, mul_comm]
      _ ≤ K * (GrowthLemmas.multifoldSumset fold
            (insert 0 A)).card := hdouble
      _ ≤ K * (C * (GrowthLemmas.multifoldSumset fold
            (insert 0 B)).card) := by gcongr
      _ = K * C * minimumMultifoldCardinality A deletionBudget fold := by
        rw [hBmin]
        ring
  have hminimumCurrent :
      minimumMultifoldCardinality A deletionBudget fold ≤
        2 * positiveDyadicThreshold A deletionBudget h := by
    simpa only [fold] using
      minimumMultifoldCardinality_le_two_mul_positiveDyadicThreshold
        A deletionBudget h
  have hpositiveCurrent :
      1 ≤ positiveDyadicThreshold A deletionBudget h :=
    positiveDyadicThreshold_pos A deletionBudget h
  calc
    positiveDyadicThreshold A deletionBudget (h + 1) ≤
        minimumMultifoldCardinality A deletionBudget (2 ^ (h + 1)) + 1 := by
      simp only [positiveDyadicThreshold, dyadicThreshold, foldThreshold]
      omega
    _ ≤ K * C * minimumMultifoldCardinality A deletionBudget fold + 1 :=
      Nat.add_le_add_right hnextMin 1
    _ ≤ K * C *
          (2 * positiveDyadicThreshold A deletionBudget h) +
        positiveDyadicThreshold A deletionBudget h := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_left (K * C) hminimumCurrent) hpositiveCurrent
    _ = (2 * (6 * scaleDen) ^ D * (4 * (4 * scaleDen) ^ D) + 1) *
        positiveDyadicThreshold A deletionBudget h := by
      dsimp only [K, C]
      ring

/-- The complete finite bin-counting engine specialized to the actual
positive dyadic thresholds.  In contrast with
`greedy_final_dyadic_scale_lower_bound`, the high-fold input is no longer
an assumption: it follows from the minimizing definition of
`positiveDyadicThreshold` as long as all deletions stay within the source
budget. -/
theorem greedy_final_dyadic_scale_lower_bound_of_positiveDyadicThreshold
    {A : Finset ℤ} {steps terminalLevel deletionBudget ratio : ℕ}
    (binStart binLength : ℕ → ℕ)
    (hsteps : steps ≤ A.card)
    (hbudget : steps ≤ deletionBudget)
    (hcover : steps =
      ∑ h ∈ Finset.range (terminalLevel + 1), binLength h)
    (hblocks : ∀ h ≤ terminalLevel,
      binStart h + binLength h ≤ steps)
    (hratio : ∀ h ≤ terminalLevel,
      positiveDyadicThreshold A deletionBudget (h + 1) ≤
        ratio * positiveDyadicThreshold A deletionBudget h)
    (hbin : ∀ h ≤ terminalLevel, ∀ i < binLength h,
      positiveDyadicThreshold A deletionBudget h ≤
          (sums A (binStart h + i)).card ∧
        (sums A (binStart h + i)).card <
          positiveDyadicThreshold A deletionBudget (h + 1)) :
    steps ≤ 16 * ratio * 2 ^ terminalLevel := by
  have hlength : ∀ h ≤ terminalLevel,
      binLength h ≤ (8 * ratio) * 2 ^ h := by
    intro h hh
    by_cases hz : binLength h = 0
    · simp [hz]
    · have hpos : 0 < binLength h := Nat.pos_of_ne_zero hz
      have hrun := greedy_threshold_run_length_le_of_positiveDyadicThreshold
        hpos ((hblocks h hh).trans hsteps) ((hblocks h hh).trans hbudget)
        (hratio h hh) (hbin h hh)
      calc
        binLength h ≤ 4 * ratio * 2 ^ (h + 1) := hrun
        _ = (8 * ratio) * 2 ^ h := by rw [pow_succ]; ring
  have htotal : steps ≤
      (8 * ratio) * (2 ^ (terminalLevel + 1) - 1) := by
    rw [hcover]
    exact sum_bin_lengths_le binLength hlength
  calc
    steps ≤ (8 * ratio) * (2 ^ (terminalLevel + 1) - 1) := htotal
    _ ≤ (8 * ratio) * 2 ^ (terminalLevel + 1) :=
      Nat.mul_le_mul_left (8 * ratio) (Nat.sub_le _ _)
    _ = 16 * ratio * 2 ^ terminalLevel := by rw [pow_succ]; ring

end Erdos186.CFP.Greedy
