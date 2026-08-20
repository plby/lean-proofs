/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperDiscreteTCover

/-!
# Erdős Problem 446: the elementary dyadic alternative

This file proves the purely discrete geometric-series step behind Ford's
alternative (32j).  It is deliberately separated from the subsequent volume
estimate: only monotonicity of occupancy prefixes and a finite weighted
geometric sum are used here.
-/

namespace Erdos446

open Finset
open scoped BigOperators

private theorem sum_two_pow_range_alt (q : ℕ) :
    (∑ t ∈ Finset.range q, 2 ^ t) = 2 ^ q - 1 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have hpos : 0 < 2 ^ q := by positivity
      omega

/-- The small numerical inequality which supplies the slack in the dyadic
geometric-series argument. -/
private theorem six_mul_add_one_lt_five_mul_two_pow_sub_three
    {H : ℕ} (hH : 6 ≤ H) :
    6 * H + 1 < 5 * 2 ^ (H - 3) := by
  induction H, hH using Nat.le_induction with
  | base => norm_num
  | succ H hH ih =>
      have hsub : H + 1 - 3 = (H - 3) + 1 := by omega
      rw [hsub, pow_succ]
      omega

/-- The final numerical form of the geometric-series contradiction. -/
private theorem dyadic_geometric_numeric
    {H q : ℕ} (hH : 6 ≤ H) (hq : 1 ≤ q) :
    2 ^ (H - 3) + 2 * (q + H - 1) +
          2 ^ (H - 3) * 2 ^ q + 2 * H * 2 ^ q + 1 <
        2 ^ (q + H - 1) := by
  let B := 2 ^ (H - 3)
  have hbase : 6 * H + 1 < 5 * B := by
    simpa [B] using
      six_mul_add_one_lt_five_mul_two_pow_sub_three hH
  have hcoef : B + 2 * H + 2 ≤ 4 * B := by
    omega
  have htarget (j : ℕ) :
      2 ^ (j + 1 + H - 1) = 4 * B * 2 ^ (j + 1) := by
    rw [show j + 1 + H - 1 = (H - 3) + 2 + (j + 1) by omega,
      pow_add, pow_add]
    simp [B]
    ring
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hq
  simp only [Nat.one_add]
  change B + 2 * (j + 1 + H - 1) + B * 2 ^ (j + 1) +
      2 * H * 2 ^ (j + 1) + 1 < 2 ^ (j + 1 + H - 1)
  rw [htarget]
  induction j with
  | zero =>
      norm_num [pow_succ]
      omega
  | succ j ih =>
      have hp : 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by
        rw [pow_succ]
        ring
      have ih' := ih (by omega : 1 ≤ 1 + j)
      have hx0 : j + 1 + H - 1 = j + H := by omega
      have hx1 : j + 1 + 1 + H - 1 = j + H + 1 := by omega
      rw [hx0] at ih'
      rw [hp]
      rw [hx1]
      calc
        B + 2 * (j + H + 1) + B * (2 * 2 ^ (j + 1)) +
              2 * H * (2 * 2 ^ (j + 1)) + 1 ≤
            2 * (B + 2 * (j + H) + B * 2 ^ (j + 1) +
              2 * H * 2 ^ (j + 1) + 1) := by
                nlinarith
        _ < 2 * (4 * B * 2 ^ (j + 1)) :=
          (Nat.mul_lt_mul_left (by omega : 0 < 2)).mpr ih'
        _ = 4 * B * (2 * 2 ^ (j + 1)) := by ring

/-- If every candidate dyadic crowding event fails, then the deficit in any
prefix is bounded by a fixed top strip plus twice its distance from the
singular exponent. -/
private theorem prefixDeficit_le_of_no_dyadicCrowding
    {v : ℕ} (c : Fin v → ℕ) {q γ H l s : ℕ}
    (hl : l = blockPrefixCount c q)
    (hdepth : H = l - γ - q + 1)
    (hH : 6 ≤ H) (hs : s ≤ q)
    (hno : ∀ m, H - 3 ≤ m → 2 ^ m < l →
      l - 2 ^ m ≤ blockPrefixCount c (l - γ - 2 ^ m)) :
    l - blockPrefixCount c s ≤
      2 ^ (H - 3) + 2 * ((l - γ) - s) := by
  have hHpos : 0 < H := by omega
  have hn : l - γ = q + H - 1 := by omega
  let A := (l - γ) - s
  have hApos : 0 < A := by
    dsimp [A]
    omega
  let e := (Nat.log 2 A).succ
  have hAlt : A < 2 ^ e := by
    exact Nat.lt_pow_succ_log_self (by omega) A
  have heceil : 2 ^ e ≤ 2 * A := by
    rw [show e = Nat.log 2 A + 1 by rfl, pow_succ]
    have := Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 hApos.ne')
    simpa [Nat.mul_comm] using this
  by_cases he : e ≤ H - 3
  · let m := H - 3
    have hm : H - 3 ≤ m := le_rfl
    have hAg : A < 2 ^ m :=
      hAlt.trans_le (Nat.pow_le_pow_right (by omega) he)
    have hgBound : 2 ^ m ≤ 2 ^ (H - 3) + 2 * A := by
      simp [m]
    by_cases hgl : 2 ^ m < l
    · have hprefix := hno m hm hgl
      have hindex : l - γ - 2 ^ m ≤ s := by
        dsimp [A] at hAg
        omega
      have hmono := blockPrefixCount_monotone c hindex
      omega
    · have hlg : l ≤ 2 ^ m := Nat.le_of_not_gt hgl
      have hzero : 0 ≤ blockPrefixCount c s := Nat.zero_le _
      omega
  · let m := e
    have hm : H - 3 ≤ m := by
      dsimp [m]
      omega
    have hAg : A < 2 ^ m := by simpa [m] using hAlt
    have hgBound : 2 ^ m ≤ 2 ^ (H - 3) + 2 * A := by
      have hmceil : 2 ^ m ≤ 2 * A := by simpa [m] using heceil
      exact hmceil.trans (Nat.le_add_left _ _)
    by_cases hgl : 2 ^ m < l
    · have hprefix := hno m hm hgl
      have hindex : l - γ - 2 ^ m ≤ s := by
        dsimp [A] at hAg
        omega
      have hmono := blockPrefixCount_monotone c hindex
      omega
    · have hlg : l ≤ 2 ^ m := Nat.le_of_not_gt hgl
      have hzero : 0 ≤ blockPrefixCount c s := Nat.zero_le _
      omega

/-- The direct discrete form of Ford's assertion (32j).  A weighted-prefix
singularity whose affine depth is at least six forces a dyadic crowding
witness at some exponent `m ≥ H - 3`. -/
theorem exists_fordDyadicCrowdingEvent_of_weighted_singularity
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
      blockPrefixCount c
          (blockPrefixCount c q - γ - 2 ^ m) <
        blockPrefixCount c q - 2 ^ m := by
  let l := blockPrefixCount c q
  let H := l - γ - q + 1
  have hH : 6 ≤ H := by omega
  have hn : l - γ = q + H - 1 := by
    dsimp [H]
    omega
  have hq : 1 ≤ q := by
    by_contra hq0
    have hqzero : q = 0 := by omega
    subst q
    simp [l, H, blockPrefixCount] at hH
  by_contra hex
  have hno : ∀ m, H - 3 ≤ m → 2 ^ m < l →
      l - 2 ^ m ≤ blockPrefixCount c (l - γ - 2 ^ m) := by
    intro m hm hml
    by_contra hlt
    apply hex
    refine ⟨m, ?_, ?_, ?_⟩
    · change H - 3 ≤ m
      exact hm
    · change 2 ^ m < l
      exact hml
    · change blockPrefixCount c (l - γ - 2 ^ m) < l - 2 ^ m
      exact Nat.lt_of_not_ge hlt
  have hdeficit (s : ℕ) (hs : s ≤ q) :
      l - blockPrefixCount c s ≤
        2 ^ (H - 3) + 2 * ((l - γ) - s) :=
    prefixDeficit_le_of_no_dyadicCrowding c rfl rfl hH hs hno
  have hlbound : l ≤ 2 ^ (H - 3) + 2 * (q + H - 1) := by
    have h := hdeficit 0 (Nat.zero_le q)
    simpa [blockPrefixCount, hn] using h
  have htail :
      (∑ t ∈ Finset.range q,
          (l - blockPrefixCount c (t + 1)) * 2 ^ t) ≤
        2 ^ (H - 3) * 2 ^ q + 2 * H * 2 ^ q := by
    calc
      (∑ t ∈ Finset.range q,
          (l - blockPrefixCount c (t + 1)) * 2 ^ t) ≤
          ∑ t ∈ Finset.range q,
            (2 ^ (H - 3) + 2 * ((q + H - 2) - t)) * 2 ^ t := by
        apply Finset.sum_le_sum
        intro t ht
        apply Nat.mul_le_mul_right
        have htq : t + 1 ≤ q := by
          have := Finset.mem_range.mp ht
          omega
        have hd := hdeficit (t + 1) htq
        rw [hn] at hd
        have hrewrite : q + H - 1 - (t + 1) = q + H - 2 - t := by
          omega
        simpa [hrewrite] using hd
      _ = 2 ^ (H - 3) * (2 ^ q - 1) +
            2 * (∑ t ∈ Finset.range q, (q + H - 2 - t) * 2 ^ t) := by
        calc
          (∑ t ∈ Finset.range q,
              (2 ^ (H - 3) + 2 * (q + H - 2 - t)) * 2 ^ t) =
              (∑ t ∈ Finset.range q, 2 ^ (H - 3) * 2 ^ t) +
                ∑ t ∈ Finset.range q,
                  2 * ((q + H - 2 - t) * 2 ^ t) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro t ht
            ring
          _ = 2 ^ (H - 3) * (∑ t ∈ Finset.range q, 2 ^ t) +
                2 * (∑ t ∈ Finset.range q,
                  (q + H - 2 - t) * 2 ^ t) := by
            rw [Finset.mul_sum, Finset.mul_sum]
          _ = _ := by rw [sum_two_pow_range_alt]
      _ ≤ 2 ^ (H - 3) * 2 ^ q + 2 * (H * 2 ^ q) := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        · apply Nat.mul_le_mul_left 2
          have hw := weightedTwoPowRange_le
            (A := q + H - 2) (T := q) (by omega)
          have heq : q + H - 2 - q + 2 = H := by omega
          simpa [heq] using hw
      _ = 2 ^ (H - 3) * 2 ^ q + 2 * H * 2 ^ q := by ring
  have hweight :
      blockPrefixWeight c q + 1 < 2 ^ (q + H - 1) := by
    rw [blockPrefixWeight_eq_count_add_tailSum]
    change l +
        (∑ t ∈ Finset.range q,
          (l - blockPrefixCount c (t + 1)) * 2 ^ t) + 1 < _
    apply lt_of_le_of_lt
      (Nat.add_le_add_right (Nat.add_le_add hlbound htail) 1)
    have hnum := dyadic_geometric_numeric hH hq
    omega
  have hpow : 2 ^ l = 2 ^ γ * 2 ^ (q + H - 1) := by
    rw [← pow_add, ← hn]
    have hγl : γ ≤ l := by omega
    rw [Nat.add_sub_of_le hγl]
  rw [hpow] at hsingular
  have hpositive : 0 < 2 ^ γ := by positivity
  have := Nat.le_of_mul_le_mul_left hsingular hpositive
  omega

end Erdos446
