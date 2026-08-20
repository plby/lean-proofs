/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedLowerCaps
import ErdosProblems.Erdos446.SizedCompositions
import Mathlib.Data.Fin.Rev

/-!
# Erdős Problem 446: reverse caps imply the construction size bound

The forward one-slack Smirnov barrier makes Ford's ordinary block cap
automatic, but it does not control the weighted size of the last blocks.
This file introduces the reverse linear cap used for that purpose.  Its
constant `4` is chosen so that the elementary geometric series gives the
exact threshold in `sizedCappedCompositions`.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- Linear cap read from the last block backwards. -/
def IsFixedLowerReverseCapped {k : ℕ} (c : Fin k → ℕ) : Prop :=
  ∀ j : Fin k, c j.rev ≤ 4 * (j.val + 1)

instance decidableIsFixedLowerReverseCapped {k : ℕ} (c : Fin k → ℕ) :
    Decidable (IsFixedLowerReverseCapped c) := by
  unfold IsFixedLowerReverseCapped
  infer_instance

theorem two_pow_rev_eq_div {k : ℕ} (j : Fin k) :
    (2 : ℝ) ^ j.rev.val = (2 : ℝ) ^ k / (2 : ℝ) ^ (j.val + 1) := by
  have hsum : j.rev.val + (j.val + 1) = k := by
    simp only [Fin.val_rev]
    omega
  apply (eq_div_iff (by positivity : (2 : ℝ) ^ (j.val + 1) ≠ 0)).2
  rw [← pow_add, hsum]

/-- The reverse linear cap gives twice the room required by the formal
construction-size cutoff. -/
theorem compositionSizeCost_le_eight_two_pow_of_reverseCapped
    {k : ℕ} {c : Fin k → ℕ} (hc : IsFixedLowerReverseCapped c) :
    compositionSizeCost c ≤ 8 * (2 : ℝ) ^ k := by
  have hreindex :
      compositionSizeCost c =
        ∑ j : Fin k, (c j.rev : ℝ) * (2 : ℝ) ^ j.rev.val := by
    rw [compositionSizeCost]
    simpa only [Fin.revPerm_apply] using
      (Equiv.sum_comp (@Fin.revPerm k)
        (fun i : Fin k ↦ (c i : ℝ) * (2 : ℝ) ^ i.val)).symm
  rw [hreindex]
  calc
    (∑ j : Fin k, (c j.rev : ℝ) * (2 : ℝ) ^ j.rev.val) ≤
        ∑ j : Fin k,
          (4 * ((j.val + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ j.rev.val := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc j) (by positivity)
    _ = 4 * (2 : ℝ) ^ k *
        ∑ j : Fin k, ((j.val + 1 : ℕ) : ℝ) /
          (2 : ℝ) ^ (j.val + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [two_pow_rev_eq_div]
      ring
    _ ≤ 4 * (2 : ℝ) ^ k * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (∑ j : Fin k, ((j.val + 1 : ℕ) : ℝ) /
            (2 : ℝ) ^ (j.val + 1)) =
            (1 / 2 : ℝ) *
              ∑ j ∈ Finset.range k,
                ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ j := by
          rw [← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [pow_succ]
          ring
        _ ≤ (1 / 2 : ℝ) * 4 :=
          mul_le_mul_of_nonneg_left (weighted_geometric_one_le k) (by norm_num)
        _ = 2 := by norm_num
    _ = 8 * (2 : ℝ) ^ k := by ring

theorem compositionSizeCost_le_sixteen_two_pow_of_reverseCapped
    {k : ℕ} {c : Fin k → ℕ} (hc : IsFixedLowerReverseCapped c) :
    compositionSizeCost c ≤ 16 * (2 : ℝ) ^ k := by
  exact (compositionSizeCost_le_eight_two_pow_of_reverseCapped hc).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))

/-- A one-slack occupancy satisfying the reverse cap belongs to the exact
`sizedCappedCompositions` family used by `SizedBlockBounds`. -/
theorem mem_sizedCappedCompositions_of_smirnov_reverseCapped
    {M k : ℕ} (hM : 1 ≤ M) {c : Fin k → ℕ}
    (hc : c ∈ smirnovOccupancies k 1 k)
    (hrev : IsFixedLowerReverseCapped c) :
    c ∈ sizedCappedCompositions M k := by
  rw [mem_sizedCappedCompositions]
  exact ⟨mem_cappedCompositions.mpr
      ⟨(mem_smirnovOccupancies_iff_barrier.mp hc).1,
        smirnovOccupancy_one_isFordCapped hM hc⟩,
    compositionSizeCost_le_sixteen_two_pow_of_reverseCapped hrev⟩

end Erdos446
