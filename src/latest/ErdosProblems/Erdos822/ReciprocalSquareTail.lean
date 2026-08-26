/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.PSeries

/-!
# A finite reciprocal-square tail

The determinant-prime charge in the small common-divisor range is summed
over a finite set of integers above a cutoff.  Primality and divisibility
only shrink that set, so the elementary telescoping bound for
`sum 1 / n^2` gives the required uniform estimate.
-/

namespace Erdos822

open scoped BigOperators

/-- Every finite collection of integers in `(y,U]` has reciprocal-square
mass at most `1/y`.  This is the form used for determinant-prime charges. -/
theorem sum_inv_sq_le_inv_of_subset_Ioc
    {S : Finset ℕ} {y U : ℕ} (hy : 1 ≤ y)
    (hS : S ⊆ Finset.Ioc y U) :
    ∑ p ∈ S, (1 : ℝ) / (p ^ 2 : ℕ) ≤ (1 : ℝ) / y := by
  by_cases hyU : y ≤ U
  · calc
      (∑ p ∈ S, (1 : ℝ) / (p ^ 2 : ℕ)) ≤
          ∑ n ∈ Finset.Ioc y U, (1 : ℝ) / (n ^ 2 : ℕ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hS
        intro n hn hnot
        positivity
      _ ≤ (1 : ℝ) / y - (1 : ℝ) / U := by
        have h :=
          (sum_Ioc_inv_sq_le_sub (α := ℝ) (k := y) (n := U)
            (by omega) hyU)
        norm_num only [one_div, Nat.cast_pow] at h ⊢
        push_cast at h
        exact h
      _ ≤ (1 : ℝ) / y := by
        have hnonneg : 0 ≤ (1 : ℝ) / U := by positivity
        linarith
  · have hIoc : Finset.Ioc y U = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨n, hn⟩
      have hnData := Finset.mem_Ioc.mp hn
      omega
    have hEmpty : S = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨n, hn⟩
      have := hS hn
      simpa [hIoc] using this
    simp [hEmpty]

end Erdos822
