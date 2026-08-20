/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedDyadicLower

/-!
# Erdős Problem 446: selecting the construction depth

The construction scales grow by squaring.  For every sufficiently large
endpoint, `fordScaleDepth M y` is therefore a positive maximal depth whose
scale is at most `y`; the next scale is already larger than `y`.
-/

namespace Erdos446

/-- The largest construction depth, searched up to the harmless bound `y`,
whose required size scale does not exceed `y`. -/
def fordScaleDepth (M y : ℕ) : ℕ :=
  Nat.findGreatest (fun K ↦ fordConstructionScale M K ≤ y) y

theorem fordConstructionScale_succ (M K : ℕ) :
    fordConstructionScale M (K + 1) = fordConstructionScale M K ^ 2 := by
  change 2 ^ (128 * 2 ^ (M + (K + 1))) =
    (2 ^ (128 * 2 ^ (M + K))) ^ 2
  rw [show M + (K + 1) = (M + K) + 1 by omega, pow_succ, ← pow_mul]
  congr 1
  ring

theorem depth_lt_fordConstructionScale (M K : ℕ) :
    K < fordConstructionScale M K := by
  have hself : K < 2 ^ K := K.lt_two_pow_self
  have hexp : K ≤ 128 * 2 ^ (M + K) := by
    calc
      K ≤ 2 ^ K := hself.le
      _ ≤ 2 ^ (M + K) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ 128 * 2 ^ (M + K) :=
        Nat.le_mul_of_pos_left _ (by omega)
  exact hself.trans_le (by
    dsimp [fordConstructionScale]
    exact Nat.pow_le_pow_right (by omega) hexp)

theorem fordScaleDepth_pos {M y : ℕ}
    (hy : fordConstructionScale M 1 ≤ y) :
    0 < fordScaleDepth M y := by
  have h1y : 1 ≤ y := by
    exact (depth_lt_fordConstructionScale M 1).le.trans hy
  exact zero_lt_one.trans_le (Nat.le_findGreatest
    (P := fun K ↦ fordConstructionScale M K ≤ y) h1y hy)

theorem fordScaleDepth_scale_le {M y : ℕ}
    (hy : fordConstructionScale M 1 ≤ y) :
    fordConstructionScale M (fordScaleDepth M y) ≤ y := by
  have h1y : 1 ≤ y := by
    exact (depth_lt_fordConstructionScale M 1).le.trans hy
  exact Nat.findGreatest_spec
    (P := fun K ↦ fordConstructionScale M K ≤ y) h1y hy

theorem fordScaleDepth_lt_next_scale {M y : ℕ}
    (hy : fordConstructionScale M 1 ≤ y) :
    y < fordConstructionScale M (fordScaleDepth M y + 1) := by
  have hscale := fordScaleDepth_scale_le hy
  have hsuccY : fordScaleDepth M y + 1 ≤ y := by
    have hdepthLt : fordScaleDepth M y < y :=
      (depth_lt_fordConstructionScale M (fordScaleDepth M y)).trans_le hscale
    omega
  exact Nat.lt_of_not_ge (Nat.findGreatest_is_greatest
    (P := fun K ↦ fordConstructionScale M K ≤ y)
    (Nat.lt_succ_self _) hsuccY)

theorem fordScaleDepth_interval {M y : ℕ}
    (hy : fordConstructionScale M 1 ≤ y) :
    fordConstructionScale M (fordScaleDepth M y) ≤ y ∧
      y < fordConstructionScale M (fordScaleDepth M y) ^ 2 := by
  exact ⟨fordScaleDepth_scale_le hy, by
    rw [← fordConstructionScale_succ]
    exact fordScaleDepth_lt_next_scale hy⟩

end Erdos446
