/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.PartitionBookkeeping

/-!
# Real-power estimates for cell line counts

This file contains the elementary maximum-times-sum estimate used to sum
the inductive contribution of the good cells.
-/

open scoped BigOperators

namespace Erdos95.RpowBookkeeping

/-- If `c a_i ≤ M` and `∑ a_i ≤ W M`, then the `p`-moment is bounded
by the maximum `(M/c)^(p-1)` times the first moment. -/
theorem sum_natCast_rpow_le_of_mul_le
    {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    (M c W : ℕ) (p : ℝ) (hp : 1 ≤ p) (hc : 0 < c)
    (hpoint : ∀ i ∈ s, c * a i ≤ M)
    (hsum : ∑ i ∈ s, a i ≤ W * M) :
    (∑ i ∈ s, ((a i : ℕ) : ℝ) ^ p) ≤
      ((M : ℝ) / (c : ℝ)) ^ (p - 1) * ((W * M : ℕ) : ℝ) := by
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpminus : 0 ≤ p - 1 := sub_nonneg.mpr hp
  have hterm : ∀ i ∈ s,
      ((a i : ℕ) : ℝ) ^ p ≤
        ((M : ℝ) / (c : ℝ)) ^ (p - 1) * (a i : ℝ) := by
    intro i hi
    by_cases hai : a i = 0
    · simp [hai, Real.zero_rpow hp0]
    · have haiR : 0 < (a i : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hai
      have hcast : (c : ℝ) * (a i : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast hpoint i hi
      have hquot : (a i : ℝ) ≤ (M : ℝ) / (c : ℝ) := by
        exact (le_div_iff₀ hcR).mpr (by simpa [mul_comm] using hcast)
      calc
        ((a i : ℕ) : ℝ) ^ p =
            (a i : ℝ) ^ (1 + (p - 1)) := by ring_nf
        _ = (a i : ℝ) * (a i : ℝ) ^ (p - 1) := by
          rw [Real.rpow_add haiR]
          simp
        _ ≤ (a i : ℝ) *
            (((M : ℝ) / (c : ℝ)) ^ (p - 1)) := by
          gcongr
        _ = ((M : ℝ) / (c : ℝ)) ^ (p - 1) *
            (a i : ℝ) := by ring
  calc
    (∑ i ∈ s, ((a i : ℕ) : ℝ) ^ p) ≤
        ∑ i ∈ s,
          ((M : ℝ) / (c : ℝ)) ^ (p - 1) * (a i : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hterm i hi
    _ = ((M : ℝ) / (c : ℝ)) ^ (p - 1) *
        ∑ i ∈ s, (a i : ℝ) := by rw [Finset.mul_sum]
    _ ≤ ((M : ℝ) / (c : ℝ)) ^ (p - 1) *
        ((W * M : ℕ) : ℝ) := by
      gcongr
      exact_mod_cast hsum

end Erdos95.RpowBookkeeping
