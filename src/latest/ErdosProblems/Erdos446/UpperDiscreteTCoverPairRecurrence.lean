/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperDiscreteTCover

/-!
# Erdős Problem 446: pairing a discrete prefix tail

This file records the elementary recurrence used at the corrected Ford
cutoff.  Reading the weighted tail backwards in pairs, the deficit at the
earlier endpoint of a pair controls both terms.  The assumed loss of one
power of two from one pair to the next is then summable.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- Pairwise summation of a prefix deficit.  The hypothesis samples the
deficit at every other prefix, starting at `Q - 1`.  Monotonicity of prefix
counts controls the intervening term, and the resulting geometric series
has the explicit constant three. -/
theorem two_mul_prefixDeficitSum_le_three_mul_two_pow
    {v : ℕ} (c : Fin v → ℕ) (l Q s : ℕ)
    (hdeficit : ∀ j : ℕ,
      l - blockPrefixCount c (Q - 1 - 2 * j) ≤ 2 ^ (s + j)) :
    2 * (∑ t ∈ Finset.range Q,
      (l - blockPrefixCount c (t + 1)) * 2 ^ t) ≤
      3 * 2 ^ (Q + s) := by
  induction Q using Nat.strong_induction_on generalizing s with
  | h Q ih =>
      cases Q with
      | zero => simp
      | succ Q =>
          cases Q with
          | zero =>
              have hmono : blockPrefixCount c 0 ≤ blockPrefixCount c 1 :=
                blockPrefixCount_monotone c (by omega)
              have hfirst : l - blockPrefixCount c 1 ≤ 2 ^ s := by
                have hzero := hdeficit 0
                have hzero' : l - blockPrefixCount c 0 ≤ 2 ^ s := by
                  simpa using hzero
                exact (Nat.sub_le_sub_left hmono l).trans hzero'
              simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
                pow_zero, mul_one]
              calc
                2 * (l - blockPrefixCount c 1) ≤ 2 * 2 ^ s :=
                  Nat.mul_le_mul_left 2 hfirst
                _ ≤ 3 * 2 ^ (1 + s) := by
                  rw [show 1 + s = s + 1 by omega, pow_succ]
                  omega
          | succ n =>
              have hrecDeficit : ∀ j : ℕ,
                  l - blockPrefixCount c (n - 1 - 2 * j) ≤
                    2 ^ ((s + 1) + j) := by
                intro j
                have hj := hdeficit (j + 1)
                have hindex :
                    n + 1 + 1 - 1 - 2 * (j + 1) = n - 1 - 2 * j := by
                  omega
                rw [hindex] at hj
                convert hj using 1
                congr 1
                omega
              have hrec := ih n (by omega) (s + 1) hrecDeficit
              have hmonoLast :
                  blockPrefixCount c (n + 1) ≤ blockPrefixCount c (n + 2) :=
                blockPrefixCount_monotone c (by omega)
              have hfirst : l - blockPrefixCount c (n + 1) ≤ 2 ^ s := by
                have hzero := hdeficit 0
                simpa using hzero
              have hsecond : l - blockPrefixCount c (n + 2) ≤ 2 ^ s := by
                omega
              have htail :
                  2 * ((l - blockPrefixCount c (n + 1)) * 2 ^ n +
                    (l - blockPrefixCount c (n + 2)) * 2 ^ (n + 1)) ≤
                    3 * 2 ^ (n + (s + 1)) := by
                calc
                  2 * ((l - blockPrefixCount c (n + 1)) * 2 ^ n +
                      (l - blockPrefixCount c (n + 2)) * 2 ^ (n + 1)) ≤
                      2 * (2 ^ s * 2 ^ n + 2 ^ s * 2 ^ (n + 1)) :=
                    Nat.mul_le_mul_left 2 <|
                      Nat.add_le_add
                        (Nat.mul_le_mul_right (2 ^ n) hfirst)
                        (Nat.mul_le_mul_right (2 ^ (n + 1)) hsecond)
                  _ = 3 * 2 ^ (n + (s + 1)) := by
                    rw [pow_succ, pow_add, pow_succ]
                    ring
              rw [Finset.sum_range_succ, Finset.sum_range_succ]
              calc
                2 * ((∑ t ∈ Finset.range n,
                      (l - blockPrefixCount c (t + 1)) * 2 ^ t) +
                    (l - blockPrefixCount c (n + 1)) * 2 ^ n +
                    (l - blockPrefixCount c (n + 2)) * 2 ^ (n + 1)) =
                    2 * (∑ t ∈ Finset.range n,
                      (l - blockPrefixCount c (t + 1)) * 2 ^ t) +
                    2 * ((l - blockPrefixCount c (n + 1)) * 2 ^ n +
                      (l - blockPrefixCount c (n + 2)) * 2 ^ (n + 1)) := by
                  ring
                _ ≤ 3 * 2 ^ (n + (s + 1)) + 3 * 2 ^ (n + (s + 1)) :=
                  Nat.add_le_add hrec htail
                _ = 3 * 2 ^ (n + 2 + s) := by
                  rw [show n + 2 + s = (n + (s + 1)) + 1 by omega, pow_succ]
                  ring

end Erdos446
