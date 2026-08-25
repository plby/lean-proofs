/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.LargePrimeResidueBlocks

/-!
# The harmonic kernel from additive prime blocks

After the progression sieve is applied to a block of width L, division by
the left endpoint jL produces a 1/j kernel.  This file isolates the real
algebra, including the floor in L / p.
-/

namespace Erdos822

open scoped BigOperators

/-- One width-L block is bounded by the expected harmonic kernel. -/
theorem blockKernel_le_harmonicTerm
    {L p j : ℕ} {W E : ℝ}
    (hL : 0 < L) (hp : 0 < p) (hjp : 1 ≤ j) (hpL : p ≤ L)
    (hW : 0 ≤ W) (hE : 0 ≤ E) :
    ((((L / p + 1 : ℕ) : ℝ) * W + E) /
        (((j * L + 1 : ℕ) : ℝ))) ≤
      (2 * W / (p : ℝ) + E / (L : ℝ)) * ((1 : ℝ) / (j : ℝ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hjR : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hcast :
      ((L / p + 1 : ℕ) : ℝ) ≤ (L : ℝ) / (p : ℝ) + 1 := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    simpa [add_comm] using
      (add_le_add_right
        (Nat.cast_div_le (α := ℝ) (m := L) (n := p)) 1)
  have hone : (1 : ℝ) ≤ (L : ℝ) / p := by
    apply (le_div_iff₀ hpR).2
    norm_num
    exact_mod_cast hpL
  have hcoeff :
      ((L / p + 1 : ℕ) : ℝ) ≤ 2 * (L : ℝ) / (p : ℝ) := by
    calc
      ((L / p + 1 : ℕ) : ℝ) ≤ (L : ℝ) / (p : ℝ) + 1 := hcast
      _ ≤ 2 * ((L : ℝ) / (p : ℝ)) := by linarith
      _ = 2 * (L : ℝ) / (p : ℝ) := by ring
  have hnum :
      (((L / p + 1 : ℕ) : ℝ) * W + E) ≤
        (2 * (L : ℝ) / (p : ℝ)) * W + E := by
    simpa [add_comm] using
      (add_le_add_right (mul_le_mul_of_nonneg_right hcoeff hW) E)
  have hden :
      (j : ℝ) * L ≤ ((j * L + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hjLpos : (0 : ℝ) < (j : ℝ) * L := mul_pos hjR hLR
  have hnum0 : 0 ≤ (2 * (L : ℝ) / (p : ℝ)) * W + E := by positivity
  calc
    ((((L / p + 1 : ℕ) : ℝ) * W + E) /
        (((j * L + 1 : ℕ) : ℝ))) ≤
        ((2 * (L : ℝ) / (p : ℝ)) * W + E) /
          (((j * L + 1 : ℕ) : ℝ)) := by
      exact div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ ((2 * (L : ℝ) / (p : ℝ)) * W + E) /
          ((j : ℝ) * L) := by
      exact div_le_div_of_nonneg_left hnum0 hjLpos hden
    _ = (2 * W / (p : ℝ) + E / (L : ℝ)) * ((1 : ℝ) / (j : ℝ)) := by
      field_simp

/-- Summing the preceding inequality over j=1,...,N gives one harmonic
factor. -/
theorem sum_blockKernel_le_harmonic
    {N L p : ℕ} {W E : ℝ}
    (hL : 0 < L) (hp : 0 < p) (hpL : p ≤ L)
    (hW : 0 ≤ W) (hE : 0 ≤ E) :
    ∑ j ∈ Finset.Icc 1 N,
        ((((L / p + 1 : ℕ) : ℝ) * W + E) /
          (((j * L + 1 : ℕ) : ℝ))) ≤
      (2 * W / (p : ℝ) + E / (L : ℝ)) * (harmonic N : ℝ) := by
  calc
    (∑ j ∈ Finset.Icc 1 N,
        ((((L / p + 1 : ℕ) : ℝ) * W + E) /
          (((j * L + 1 : ℕ) : ℝ)))) ≤
        ∑ j ∈ Finset.Icc 1 N,
          (2 * W / (p : ℝ) + E / (L : ℝ)) * ((1 : ℝ) / (j : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact blockKernel_le_harmonicTerm hL hp
        (Finset.mem_Icc.mp hj).1 hpL hW hE
    _ = (2 * W / (p : ℝ) + E / (L : ℝ)) * (harmonic N : ℝ) := by
      rw [← Finset.mul_sum]
      simp [harmonic_eq_sum_Icc, one_div]

end Erdos822
