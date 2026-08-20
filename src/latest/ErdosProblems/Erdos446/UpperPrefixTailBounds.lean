/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperDiscreteTCover

/-!
# Erdős Problem 446: dyadic bounds for weighted occupancy prefixes

This file supplies the finite summation lemma used in Ford's exceptional
cover.  If none of the dyadic crowding events occurs at scales `m ≥ s`,
then the number of objects after any prefix `u` is controlled at the scale

`2 ^ max s (Nat.clog 2 (A - u))`.

The maximum has two jobs: the first argument keeps the scale inside the
range covered by the no-crowding hypothesis, while the second makes the
dyadic interval reach from `A` back to `u`.  Its power is at most
`2^s + 2(A-u)`.  Combining this pointwise estimate with the summation by
parts identity from `UpperDiscreteTCover` gives a closed upper bound for
`blockPrefixWeight`.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- The least dyadic scale above `x`, enlarged to be at least `s`, is
bounded by the sum of the cutoff scale and twice `x`. -/
theorem two_pow_max_clog_le_pow_add_twice (s x : ℕ) :
    2 ^ max s (Nat.clog 2 x) ≤ 2 ^ s + 2 * x := by
  by_cases h : Nat.clog 2 x ≤ s
  · rw [max_eq_left h]
    omega
  · have hsclog : s < Nat.clog 2 x := Nat.lt_of_not_ge h
    have hclogpos : 0 < Nat.clog 2 x :=
      (Nat.zero_le s).trans_lt hsclog
    have hx : 1 < x := by
      rw [← Nat.pow_zero]
      exact (Nat.lt_clog_iff_pow_lt (by omega : 1 < 2)).mp hclogpos
    have hpred : 2 ^ (Nat.clog 2 x).pred < x :=
      Nat.pow_pred_clog_lt_self (by omega : 1 < 2) hx
    rw [max_eq_right hsclog.le]
    have hclogEq : Nat.clog 2 x = (Nat.clog 2 x).pred + 1 := by
      have := Nat.succ_pred_eq_of_pos hclogpos
      omega
    exact (calc
      2 ^ Nat.clog 2 x = 2 ^ ((Nat.clog 2 x).pred + 1) := by
        exact congrArg (fun n : ℕ ↦ 2 ^ n) hclogEq
      _ = 2 ^ (Nat.clog 2 x).pred * 2 := by rw [pow_succ]
      _ < x * 2 := (Nat.mul_lt_mul_right (by omega : 0 < 2)).mpr hpred
      _ = 2 * x := by omega
      _ ≤ 2 ^ s + 2 * x := Nat.le_add_left _ _).le

/-- Pointwise form of the dyadic no-crowding argument.  Here `A` is the
unshifted affine rank (`l-γ` in the application).  The hypothesis says
that every dyadic scale at least `s` which is smaller than `l` has at least
`l-2^m` objects before cell `A-2^m`.

The conclusion bounds the number of objects after cell `u` by the single
dyadic scale which both lies above `s` and reaches back from `A` to `u`.
-/
theorem blockPrefixTail_le_pow_max_clog
    {v : ℕ} (c : Fin v → ℕ) {l A s u : ℕ}
    (huA : u ≤ A)
    (hNoCrowding : ∀ m : ℕ, s ≤ m → 2 ^ m < l →
      l - 2 ^ m ≤ blockPrefixCount c (A - 2 ^ m)) :
    l - blockPrefixCount c u ≤
      2 ^ max s (Nat.clog 2 (A - u)) := by
  let x := A - u
  let m := max s (Nat.clog 2 x)
  have hxpow : x ≤ 2 ^ m := by
    exact (Nat.le_pow_clog (by omega : 1 < 2) x).trans
      (Nat.pow_le_pow_right (by omega : 0 < 2) (le_max_right _ _))
  have hindex : A - 2 ^ m ≤ u := by
    dsimp [x] at hxpow
    omega
  have hprefix : blockPrefixCount c (A - 2 ^ m) ≤
      blockPrefixCount c u :=
    blockPrefixCount_monotone c hindex
  by_cases hml : 2 ^ m < l
  · have hlow : l - 2 ^ m ≤ blockPrefixCount c (A - 2 ^ m) :=
      hNoCrowding m (le_max_left _ _) hml
    have := hlow.trans hprefix
    have htail : l - blockPrefixCount c u ≤ 2 ^ m := by omega
    simpa [m, x] using htail
  · have hlm : l ≤ 2 ^ m := Nat.le_of_not_gt hml
    have htail : l - blockPrefixCount c u ≤ 2 ^ m := by omega
    simpa [m, x] using htail

/-- Linearized pointwise tail bound obtained from
`blockPrefixTail_le_pow_max_clog`. -/
theorem blockPrefixTail_le_pow_add_twice_gap
    {v : ℕ} (c : Fin v → ℕ) {l A s u : ℕ}
    (huA : u ≤ A)
    (hNoCrowding : ∀ m : ℕ, s ≤ m → 2 ^ m < l →
      l - 2 ^ m ≤ blockPrefixCount c (A - 2 ^ m)) :
    l - blockPrefixCount c u ≤ 2 ^ s + 2 * (A - u) := by
  exact (blockPrefixTail_le_pow_max_clog c huA hNoCrowding).trans
    (two_pow_max_clog_le_pow_add_twice s (A - u))

private theorem upperPrefix_sum_two_pow_range (q : ℕ) :
    (∑ t ∈ Finset.range q, 2 ^ t) = 2 ^ q - 1 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have hpos : 0 < 2 ^ q := by positivity
      omega

/-- Summed form of the no-crowding estimate.  It is the direct finite
counterpart of bounding Ford's first `l` powers by a geometric series.

The strict assumption `q < A` is exactly what is needed to sum the linear
tail `A-(t+1)` with `weightedTwoPowRange_le`.
-/
theorem blockPrefixWeight_le_of_no_dyadic_crowding
    {v : ℕ} (c : Fin v → ℕ) {q l A s : ℕ}
    (hCount : blockPrefixCount c q = l) (hqA : q < A)
    (hNoCrowding : ∀ m : ℕ, s ≤ m → 2 ^ m < l →
      l - 2 ^ m ≤ blockPrefixCount c (A - 2 ^ m)) :
    blockPrefixWeight c q ≤
      l + 2 ^ s * (2 ^ q - 1) +
        2 * ((A - q + 1) * 2 ^ q) := by
  have hTail (t : ℕ) (ht : t ∈ Finset.range q) :
      l - blockPrefixCount c (t + 1) ≤
        2 ^ s + 2 * (A - (t + 1)) := by
    apply blockPrefixTail_le_pow_add_twice_gap c
    · have := Finset.mem_range.mp ht
      omega
    · exact hNoCrowding
  have hWeightedTail :
      (∑ t ∈ Finset.range q,
          (l - blockPrefixCount c (t + 1)) * 2 ^ t) ≤
        ∑ t ∈ Finset.range q,
          (2 ^ s + 2 * (A - (t + 1))) * 2 ^ t := by
    apply Finset.sum_le_sum
    intro t ht
    exact Nat.mul_le_mul_right _ (hTail t ht)
  have hGapRewrite :
      (∑ t ∈ Finset.range q, (A - (t + 1)) * 2 ^ t) =
        ∑ t ∈ Finset.range q, (A - 1 - t) * 2 ^ t := by
    apply Finset.sum_congr rfl
    intro t ht
    have := Finset.mem_range.mp ht
    have heq : A - (t + 1) = A - 1 - t := by omega
    rw [heq]
  have hqPred : q ≤ A - 1 := by omega
  have hGap :
      (∑ t ∈ Finset.range q, (A - (t + 1)) * 2 ^ t) ≤
        (A - q + 1) * 2 ^ q := by
    rw [hGapRewrite]
    have h := weightedTwoPowRange_le (A := A - 1) (T := q) hqPred
    have heq : A - 1 - q + 2 = A - q + 1 := by omega
    simpa only [heq] using h
  rw [blockPrefixWeight_eq_count_add_tailSum, hCount]
  rw [Nat.add_assoc]
  apply Nat.add_le_add_left
  calc
    (∑ t ∈ Finset.range q,
        (l - blockPrefixCount c (t + 1)) * 2 ^ t) ≤
        ∑ t ∈ Finset.range q,
          (2 ^ s + 2 * (A - (t + 1))) * 2 ^ t := hWeightedTail
    _ = 2 ^ s * (∑ t ∈ Finset.range q, 2 ^ t) +
        2 * (∑ t ∈ Finset.range q,
          (A - (t + 1)) * 2 ^ t) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ ≤ 2 ^ s * (2 ^ q - 1) +
        2 * ((A - q + 1) * 2 ^ q) := by
      rw [upperPrefix_sum_two_pow_range]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hGap) _

end Erdos446
