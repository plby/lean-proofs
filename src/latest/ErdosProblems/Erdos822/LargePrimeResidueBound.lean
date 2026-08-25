/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.BlockKernel

/-!
# Summed reciprocal bound for one large-prime residue class

The additive-block sieve estimate and the harmonic kernel now combine into
one compact inequality.  The first term has the expected inverse-modulus
factor; the second is the summed finite beta remainder.
-/

namespace Erdos822

open scoped BigOperators

theorem exists_sum_inv_largePrimeResidueClass_upper_bound :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ N p a y S : ℕ,
        2 ≤ N → p.Prime → p ≤ N ^ 21 →
        2 ≤ y → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let W :=
          (1 + eta) *
            (C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) *
              Real.exp 3)
        let E := ((y ^ S : ℕ) : ℝ) ^ 2
        ∑ q ∈ largePrimeResidueClass N p a y, (1 : ℝ) / q ≤
          (2 * W / (p : ℝ) + E / ((N ^ 21 : ℕ) : ℝ)) * (harmonic N : ℝ) := by
  obtain ⟨A, C, hA, hC, hblocks⟩ :=
    exists_sum_inv_largePrimeResidueClass_block_upper_bound
  refine ⟨A, C, hA, hC, ?_⟩
  intro N p a y S hN hp hpN hy hS hlog
  dsimp only
  let W : ℝ :=
    (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
      (C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) *
        Real.exp 3)
  let E : ℝ := ((y ^ S : ℕ) : ℝ) ^ 2
  have hW : 0 ≤ W := by
    dsimp [W]
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hlogy : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hsum := hblocks N p a y S hN hp hy hS hlog
  dsimp only at hsum
  calc
    (∑ q ∈ largePrimeResidueClass N p a y, (1 : ℝ) / q) ≤
        ∑ j ∈ Finset.Icc 1 N,
          (((N ^ 21 / p + 1 : ℕ) : ℝ) * W + E) /
            (((j * N ^ 21 + 1 : ℕ) : ℝ)) := by
      simpa [W, E, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hsum
    _ ≤ (2 * W / (p : ℝ) + E / ((N ^ 21 : ℕ) : ℝ)) * (harmonic N : ℝ) := by
      exact sum_blockKernel_le_harmonic
        (L := N ^ 21) (p := p) (W := W) (E := E)
        (by positivity) hp.pos hpN hW hE

end Erdos822
