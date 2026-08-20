/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperDiscreteTCoverPairRecurrence

/-!
# Erdős Problem 446: Ford's published linear dyadic cutoff

Ford's displayed condition (32j) uses the cell cutoff `l - γ - 2*m`,
while the number of objects in its terminal rank block is `2^m`.  This file
proves that exact finite alternative.  The proof reads the weighted prefix
backwards in pairs; `two_mul_prefixDeficitSum_le_three_mul_two_pow` is the
finite rank-block geometric series.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- The literal finite occupancy form of the cutoff in Ford's published
condition (32j). -/
def FordPublishedDyadicCrowdingEvent {v : ℕ}
    (γ m l : ℕ) (c : Fin v → ℕ) : Prop :=
  2 ^ m < l ∧
    blockPrefixCount c (l - γ - 2 * m) < l - 2 ^ m

private theorem published_sum_two_pow_range (q : ℕ) :
    (∑ t ∈ Finset.range q, 2 ^ t) = 2 ^ q - 1 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have hpos : 0 < 2 ^ q := by positivity
      omega

private theorem two_pow_sub_three_add_one_lt_two_pow
    {n : ℕ} (hn : 6 ≤ n) :
    2 ^ (n - 3) + 1 < 2 ^ n := by
  have hnEq : n = (n - 3) + 3 := by omega
  rw [hnEq, pow_add]
  norm_num
  have hp : 0 < 2 ^ (n - 3) := by positivity
  omega

private theorem two_mul_le_two_pow_of_three_le
    {m : ℕ} (hm : 3 ≤ m) : 2 * m ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      rw [pow_succ]
      omega

private theorem tail_sub_le_of_rank_lower
    {l p C : ℕ} (h : l - p ≤ C) : l - C ≤ p := by
  omega

/-- A published cutoff implies the power cutoff used by the coarser
source-compatible event.  The only input is prefix monotonicity and
`2m ≤ 2^m` for `m ≥ 3`. -/
theorem fordPublishedDyadicCrowdingEvent_implies_power_cutoff
    {v : ℕ} {c : Fin v → ℕ} {γ m l : ℕ}
    (hm : 3 ≤ m)
    (h : FordPublishedDyadicCrowdingEvent γ m l c) :
    FordPowerCutoffCrowdingEvent γ m l c := by
  rw [FordPublishedDyadicCrowdingEvent] at h
  rw [FordPowerCutoffCrowdingEvent]
  refine ⟨h.1, ?_⟩
  have h2m : 2 * m ≤ 2 ^ m := two_mul_le_two_pow_of_three_le hm
  have hindex : l - γ - 2 ^ m ≤ l - γ - 2 * m := by omega
  exact (blockPrefixCount_monotone c hindex).trans_lt h.2

/-- The exact linear-cutoff version of Ford's dyadic alternative. -/
theorem exists_fordPublishedDyadicCrowdingEvent_of_weighted_singularity
    {v : ℕ} (c : Fin v → ℕ) (q γ r : ℕ)
    (hqv : q ≤ v) (hr : 5 ≤ r)
    (hdepth : r + 1 ≤
      blockPrefixCount c q - γ - q + 1)
    (hsingular :
      2 ^ blockPrefixCount c q ≤
        2 ^ γ * (blockPrefixWeight c q + 1)) :
    ∃ m,
      (blockPrefixCount c q - γ - q + 1) - 3 ≤ m ∧
      FordPublishedDyadicCrowdingEvent γ m
        (blockPrefixCount c q) c := by
  let l := blockPrefixCount c q
  let H := l - γ - q + 1
  let n := l - γ
  let m₀ := H - 3
  let d := 2 ^ m₀
  have hH : 6 ≤ H := by omega
  have hm₀ : 3 ≤ m₀ := by
    dsimp [m₀]
    omega
  have hm₀eq : m₀ + 3 = H := by
    dsimp [m₀]
    omega
  have hn : n = q + H - 1 := by
    dsimp [n, H]
    omega
  have hq : 1 ≤ q := by
    by_contra hq0
    have hqzero : q = 0 := by omega
    subst q
    simp [l, H, blockPrefixCount] at hH
  have hnSix : 6 ≤ n := by omega
  have hpowerIdentity : 2 ^ l = 2 ^ γ * 2 ^ n := by
    rw [← pow_add]
    have hγl : γ ≤ l := by
      dsimp [n] at hn
      omega
    simp only [n]
    rw [Nat.add_sub_of_le hγl]
  have hnormalized : 2 ^ n ≤ blockPrefixWeight c q + 1 := by
    rw [hpowerIdentity] at hsingular
    exact Nat.le_of_mul_le_mul_left hsingular (by positivity)
  by_contra hex
  have hNo : ∀ m, m₀ ≤ m → 2 ^ m < l →
      l - 2 ^ m ≤ blockPrefixCount c (n - 2 * m) := by
    intro m hmm hml
    have hnot : ¬ FordPublishedDyadicCrowdingEvent γ m l c := by
      intro hevent
      apply hex
      refine ⟨m, ?_, ?_⟩
      · change m₀ ≤ m
        exact hmm
      · simpa [l] using hevent
    rw [FordPublishedDyadicCrowdingEvent] at hnot
    have hcut : ¬ blockPrefixCount c (l - γ - 2 * m) < l - 2 ^ m := by
      intro hlt
      exact hnot ⟨hml, hlt⟩
    simpa [n] using Nat.le_of_not_gt hcut
  have hdlt : d < l := by
    by_contra hnot
    have hld : l ≤ d := Nat.le_of_not_gt hnot
    have hweight := blockPrefixWeight_le_count_mul_prevPow c hq
    have hweight' : blockPrefixWeight c q ≤ 2 ^ (n - 3) := by
      calc
        blockPrefixWeight c q ≤ l * 2 ^ (q - 1) := by
          simpa [l] using hweight
        _ ≤ d * 2 ^ (q - 1) := Nat.mul_le_mul_right _ hld
        _ = 2 ^ (n - 3) := by
          change 2 ^ m₀ * 2 ^ (q - 1) = 2 ^ (n - 3)
          rw [← pow_add]
          congr 1
          omega
    have hle := hnormalized.trans (Nat.add_le_add_right hweight' 1)
    have hlt := two_pow_sub_three_add_one_lt_two_pow hnSix
    omega
  have htwom₀n : 2 * m₀ < n := by
    by_contra hnot
    have hle := hNo m₀ le_rfl hdlt
    have hzero : blockPrefixCount c (n - 2 * m₀) = 0 := by
      have : n - 2 * m₀ = 0 := by omega
      simp [this, blockPrefixCount]
    rw [hzero] at hle
    omega
  let Q := n - 2 * m₀ + 1
  have hQq : Q ≤ q := by
    dsimp [Q, m₀]
    omega
  have hdeficit : ∀ j : ℕ,
      l - blockPrefixCount c (Q - 1 - 2 * j) ≤ 2 ^ (m₀ + j) := by
    intro j
    by_cases hp : 2 ^ (m₀ + j) < l
    · have h := hNo (m₀ + j) (by omega) hp
      have hindex : Q - 1 - 2 * j = n - 2 * (m₀ + j) := by
        dsimp [Q]
        omega
      rw [hindex]
      exact tail_sub_le_of_rank_lower h
    · have hlp : l ≤ 2 ^ (m₀ + j) := Nat.le_of_not_gt hp
      exact (Nat.sub_le l _).trans hlp
  have hearly :
      2 * (∑ t ∈ Finset.range Q,
        (l - blockPrefixCount c (t + 1)) * 2 ^ t) ≤
      3 * 2 ^ (Q + m₀) :=
    two_mul_prefixDeficitSum_le_three_mul_two_pow c l Q m₀ hdeficit
  have hbasePrefix :
      l - d ≤ blockPrefixCount c (Q - 1) := by
    have h := hNo m₀ le_rfl hdlt
    have hindex : Q - 1 = n - 2 * m₀ := by
      dsimp [Q]
    simpa [d, hindex] using h
  have hlate :
      (∑ t ∈ Finset.Ico Q q,
        (l - blockPrefixCount c (t + 1)) * 2 ^ t) ≤
      d * 2 ^ q := by
    calc
      (∑ t ∈ Finset.Ico Q q,
          (l - blockPrefixCount c (t + 1)) * 2 ^ t) ≤
          ∑ t ∈ Finset.Ico Q q, d * 2 ^ t := by
        apply Finset.sum_le_sum
        intro t ht
        apply Nat.mul_le_mul_right
        have htQ : Q ≤ t := (Finset.mem_Ico.mp ht).1
        have hmono : blockPrefixCount c (Q - 1) ≤
            blockPrefixCount c (t + 1) :=
          blockPrefixCount_monotone c (by omega)
        exact tail_sub_le_of_rank_lower (hbasePrefix.trans hmono)
      _ ≤ ∑ t ∈ Finset.range q, d * 2 ^ t := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro t ht
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp ht).2
        · intro t ht hnot
          exact Nat.zero_le _
      _ = d * (2 ^ q - 1) := by
        rw [← Finset.mul_sum, published_sum_two_pow_range]
      _ ≤ d * 2 ^ q := Nat.mul_le_mul_left d (Nat.sub_le _ _)
  let tail := ∑ t ∈ Finset.range q,
    (l - blockPrefixCount c (t + 1)) * 2 ^ t
  have htailSplit :
      (∑ t ∈ Finset.range Q,
          (l - blockPrefixCount c (t + 1)) * 2 ^ t) +
        (∑ t ∈ Finset.Ico Q q,
          (l - blockPrefixCount c (t + 1)) * 2 ^ t) = tail := by
    exact Finset.sum_range_add_sum_Ico _ hQq
  have htail :
      2 * tail ≤ 3 * 2 ^ (Q + m₀) + 2 * (d * 2 ^ q) := by
    rw [← htailSplit]
    calc
      2 * ((∑ t ∈ Finset.range Q,
          (l - blockPrefixCount c (t + 1)) * 2 ^ t) +
          ∑ t ∈ Finset.Ico Q q,
            (l - blockPrefixCount c (t + 1)) * 2 ^ t) =
          2 * (∑ t ∈ Finset.range Q,
            (l - blockPrefixCount c (t + 1)) * 2 ^ t) +
          2 * (∑ t ∈ Finset.Ico Q q,
            (l - blockPrefixCount c (t + 1)) * 2 ^ t) := by ring
      _ ≤ 3 * 2 ^ (Q + m₀) + 2 * (d * 2 ^ q) :=
        Nat.add_le_add hearly (Nat.mul_le_mul_left 2 hlate)
  have hlSmall : l ≤ 2 ^ (n - 2) := by
    let M := m₀ + q
    have hM : m₀ ≤ M := by simp [M]
    have hMexp : M = n - 2 := by
      dsimp [M]
      omega
    rw [← hMexp]
    by_contra hnot
    have hp : 2 ^ M < l := lt_of_not_ge hnot
    have h := hNo M hM hp
    have hindex : n - 2 * M = 0 := by
      dsimp [M]
      omega
    rw [hindex] at h
    simp [blockPrefixCount] at h
    omega
  have hQexp : Q + m₀ = q + 3 := by
    dsimp [Q, m₀]
    omega
  have hqm : q + 3 ≤ n - 2 := by omega
  have hearlyPow : 3 * 2 ^ (Q + m₀) ≤ 3 * 2 ^ (n - 2) := by
    rw [hQexp]
    exact Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) hqm)
  have hdq : d * 2 ^ q = 2 ^ (n - 2) := by
    change 2 ^ m₀ * 2 ^ q = 2 ^ (n - 2)
    rw [← pow_add]
    congr 1
    omega
  have hP : 2 < 2 ^ (n - 2) := by
    have hexp : 1 < n - 2 := by omega
    calc
      2 = 2 ^ 1 := by norm_num
      _ < 2 ^ (n - 2) := Nat.pow_lt_pow_right (by omega) hexp
  have hweight : blockPrefixWeight c q = l + tail := by
    rw [blockPrefixWeight_eq_count_add_tailSum]
  have hdoubleWeight :
      2 * (blockPrefixWeight c q + 1) < 2 * 2 ^ n := by
    rw [hweight]
    calc
      2 * (l + tail + 1) = 2 * l + 2 * tail + 2 := by ring
      _ ≤ 2 * 2 ^ (n - 2) +
          (3 * 2 ^ (n - 2) + 2 * 2 ^ (n - 2)) + 2 := by
        gcongr
        exact htail.trans (Nat.add_le_add hearlyPow (by rw [hdq]))
      _ < 2 * 2 ^ n := by
        have hnEq : n = (n - 2) + 2 := by omega
        rw [hnEq, pow_add]
        norm_num
        omega
  have hdoubleNormalized := Nat.mul_le_mul_left 2 hnormalized
  omega

/-- The published cutoff with its two inequalities exposed literally. -/
theorem exists_fordPublishedDyadicCrowdingCutoff
    {v : ℕ} (c : Fin v → ℕ) (q γ r : ℕ)
    (hqv : q ≤ v) (hr : 5 ≤ r)
    (hdepth : r + 1 ≤
      blockPrefixCount c q - γ - q + 1)
    (hsingular :
      2 ^ blockPrefixCount c q ≤
        2 ^ γ * (blockPrefixWeight c q + 1)) :
    ∃ m,
      (blockPrefixCount c q - γ - q + 1) - 3 ≤ m ∧
      2 ^ m < blockPrefixCount c q ∧
      blockPrefixCount c (blockPrefixCount c q - γ - 2 * m) <
        blockPrefixCount c q - 2 ^ m := by
  obtain ⟨m, hm, hevent⟩ :=
    exists_fordPublishedDyadicCrowdingEvent_of_weighted_singularity
      c q γ r hqv hr hdepth hsingular
  exact ⟨m, hm, hevent.1, hevent.2⟩

/-- The same witness, repackaged in the existing power-cutoff event. -/
theorem exists_fordPowerCutoffCrowdingEvent_of_published_cutoff
    {v : ℕ} (c : Fin v → ℕ) (q γ r : ℕ)
    (hqv : q ≤ v) (hr : 5 ≤ r)
    (hdepth : r + 1 ≤
      blockPrefixCount c q - γ - q + 1)
    (hsingular :
      2 ^ blockPrefixCount c q ≤
        2 ^ γ * (blockPrefixWeight c q + 1)) :
    ∃ m,
      (blockPrefixCount c q - γ - q + 1) - 3 ≤ m ∧
      FordPowerCutoffCrowdingEvent γ m (blockPrefixCount c q) c := by
  obtain ⟨m, hm, hevent⟩ :=
    exists_fordPublishedDyadicCrowdingEvent_of_weighted_singularity
      c q γ r hqv hr hdepth hsingular
  refine ⟨m, hm, fordPublishedDyadicCrowdingEvent_implies_power_cutoff ?_ hevent⟩
  have hH : 6 ≤ blockPrefixCount c q - γ - q + 1 := by omega
  omega

end Erdos446
