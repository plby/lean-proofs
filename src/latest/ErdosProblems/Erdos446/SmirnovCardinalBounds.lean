/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovWordBarrierBridge
import ErdosProblems.Erdos446.SmirnovNumerics

/-!
# Erdős Problem 446: cardinal first-crossing bounds imply Smirnov bounds

This file is the normalization-free last step of the finite first-crossing
argument.  A lower bound for the number of failed labelled words is divided
by the total number `v^k` of words and then fed into the already proved
numerical estimate.
-/

namespace Erdos446

theorem smirnovProbability_le_exponentialComplement_of_cardinal_lower
    {k u v w : ℕ} (hv : 0 < v) (htrunc : 2 * w + 2 ≤ v)
    (hfailure :
      Real.exp (2 * (w : ℝ) + 2) *
          ((v - (2 * w + 2) : ℕ) : ℝ) ^ k ≤
        (failedBarrierWords k u v).card) :
    smirnovProbability k u v ≤
      1 - Real.exp (2 * (w : ℝ) + 2) *
        (1 - (2 * (w : ℝ) + 2) / (v : ℝ)) ^ k := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hbase : ((v - (2 * w + 2) : ℕ) : ℝ) =
      (v : ℝ) - (2 * (w : ℝ) + 2) := by
    push_cast [Nat.cast_sub htrunc]
    ring
  have hprob := smirnovProbability_le_one_sub_of_le_card_failedBarrierWords
    hv hfailure
  calc
    smirnovProbability k u v ≤
        1 - (Real.exp (2 * (w : ℝ) + 2) *
          ((v - (2 * w + 2) : ℕ) : ℝ) ^ k) /
            (v : ℝ) ^ k := hprob
    _ = 1 - Real.exp (2 * (w : ℝ) + 2) *
        (1 - (2 * (w : ℝ) + 2) / (v : ℝ)) ^ k := by
      rw [hbase, mul_div_assoc, ← div_pow]
      congr 2
      field_simp [hvR.ne']

theorem smirnovProbability_le_twentyfour_of_cardinal_lower
    {k u v w : ℕ} (hk : 100 ≤ k) (hu : 10 * u ≤ k)
    (hwSq : w * w ≤ k) (hw : 0 < w) (hrel : u + v = k + w)
    (hfailure :
      Real.exp (2 * (w : ℝ) + 2) *
          ((v - (2 * w + 2) : ℕ) : ℝ) ^ k ≤
        (failedBarrierWords k u v).card) :
    smirnovProbability k u v ≤
      24 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 / (k : ℝ) := by
  have hkR : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hwR : (w : ℝ) * w ≤ k := by exact_mod_cast hwSq
  have hwkR : 10 * (w : ℝ) ≤ k := by
    by_contra hnot
    have hlt : (k : ℝ) < 10 * w := lt_of_not_ge hnot
    nlinarith
  have hwk : 10 * w ≤ k := by exact_mod_cast hwkR
  have hv : 0 < v := by omega
  have htrunc : 2 * w + 2 ≤ v := by omega
  exact (smirnovProbability_le_exponentialComplement_of_cardinal_lower
      hv htrunc hfailure).trans
    (fordSmirnovExponentialComplement_le hk hu hwSq hrel)

end Erdos446
