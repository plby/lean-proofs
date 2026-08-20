/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovCardinalBounds
import ErdosProblems.Erdos446.SmirnovFirstCrossingSum

/-!
# Erdős Problem 446: unconditional quantitative Smirnov bound

This is the public quantitative consequence of the finite first-crossing
comparison.
-/

namespace Erdos446

theorem smirnovProbability_le_twentyfour
    {k u v w : ℕ} (hk : 100 ≤ k) (hu : 10 * u ≤ k)
    (hwSq : w * w ≤ k) (hw : 0 < w) (hrel : u + v = k + w) :
    smirnovProbability k u v ≤
      24 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 / (k : ℝ) := by
  have hkR : (100 : ℝ) ≤ k := by exact_mod_cast hk
  have hwR : (w : ℝ) * w ≤ k := by exact_mod_cast hwSq
  have hwkR : 10 * (w : ℝ) ≤ k := by
    by_contra hnot
    have hlt : (k : ℝ) < 10 * w := lt_of_not_ge hnot
    nlinarith
  have hwk : 10 * w ≤ k := by exact_mod_cast hwkR
  have htrunc : 2 * w + 2 ≤ v := by omega
  exact smirnovProbability_le_twentyfour_of_cardinal_lower
    hk hu hwSq hw hrel
      (exp_mul_truncated_words_le_card_failedBarrierWords hrel htrunc)

end Erdos446
