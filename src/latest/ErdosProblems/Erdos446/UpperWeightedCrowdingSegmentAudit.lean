/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperCrowdingMass
import ErdosProblems.Erdos446.WeightedOccupancyBridge

/-!
# Erdős Problem 446: audit of a segmentwise weighted crowding bound

A two-sided geometric estimate for the prime-block masses does not by itself
give an absolute-constant comparison between a fixed crowding segment and its
uniform reciprocal-factorial model.  A segment consisting of one cell may
contain arbitrarily many objects, and a positive error in that cell is then
raised to an arbitrarily large power.

This file records the exact extra monotonicity which would make the desired
comparison immediate: every retained block mass must be at most `log 2`.
Under that hypothesis the weighted fixed-rank crowding estimate has precisely
the same four factors as `UpperCrowdingMass`, with no parameter-dependent
tilt and no restriction relating `k` to `2^M`.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- If every cell weight is at most `L`, then on a family of occupancies of
total size `k` the weighted mass is at most `L^k` times the
reciprocal-factorial mass.  This is the monotonicity missing from a two-sided
absolute-error estimate. -/
theorem weightedOccupancyMassOver_le_const_pow_mul_reciprocal
    {v k : ℕ} {lam : Fin v → ℝ} {I : Finset (Fin v → ℕ)} {L : ℝ}
    (hlam0 : ∀ i, 0 ≤ lam i) (hlamL : ∀ i, lam i ≤ L)
    (hI : ∀ c ∈ I, ∑ i, c i = k) :
    weightedOccupancyMassOver lam I ≤
      L ^ k * reciprocalFactorialMassOver I := by
  rw [weightedOccupancyMassOver, reciprocalFactorialMassOver,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  have hprod : (∏ i : Fin v, lam i ^ c i) ≤ L ^ k := by
    calc
      (∏ i : Fin v, lam i ^ c i) ≤ ∏ i : Fin v, L ^ c i := by
        apply Finset.prod_le_prod
        · intro i hi
          exact pow_nonneg (hlam0 i) _
        · intro i hi
          exact pow_le_pow_left₀ (hlam0 i) (hlamL i) _
      _ = L ^ (∑ i, c i) := Finset.prod_pow_eq_pow_sum _ _ _
      _ = L ^ k := by rw [hI c hc]
  have hfac0 : 0 ≤ 1 / compositionFactorial c := by
    apply one_div_nonneg.mpr
    dsimp [compositionFactorial]
    positivity
  rw [weightedCompositionMass, div_eq_mul_inv, ← one_div]
  exact mul_le_mul_of_nonneg_right hprod hfac0

/-- The fixed-rank weighted crowding theorem under the missing one-sided
prime-block monotonicity.  Its right side is exactly `(log 2)^k` times the
four-factor bound in `UpperCrowdingMass`. -/
theorem weightedOccupancyMassOver_fordCrowdingOccupanciesAt_le_of_blockMass_le_log
    {M k u v g s l : ℕ}
    (hblock : ∀ i : Fin v, primeBlockMass (M + i) ≤ Real.log 2)
    (hg : 1 ≤ g) (hgl : g + 1 ≤ l) (hul : u ≤ l)
    (hlk : l ≤ k) (hhv : l - u < v) :
    weightedOccupancyMassOver (primeBlockCellMass M v)
        (fordCrowdingOccupanciesAt k u v g s l) ≤
      Real.log 2 ^ k *
        (smirnovOccupancyMass (l - g - 1) u (l - u + 1) *
          (((((l - u + 1) - (l - u - s) : ℕ) : ℝ) ^ g /
              (g.factorial : ℝ)) *
            smirnovOccupancyMass (k - l) 0 (v - (l - u)))) := by
  have hweighted :
      weightedOccupancyMassOver (primeBlockCellMass M v)
          (fordCrowdingOccupanciesAt k u v g s l) ≤
        Real.log 2 ^ k * reciprocalFactorialMassOver
          (fordCrowdingOccupanciesAt k u v g s l) := by
    apply weightedOccupancyMassOver_le_const_pow_mul_reciprocal
    · intro i
      exact primeBlockMass_nonneg _
    · intro i
      simpa only [primeBlockCellMass] using hblock i
    · intro c hc
      exact (mem_smirnovOccupancies.mp
        (mem_fordCrowdingOccupanciesAt.mp hc).1).1
  have hfour := reciprocalFactorialMassOver_fordCrowdingOccupanciesAt_le
    (s := s) hg hgl hul hlk hhv
  exact hweighted.trans
    (mul_le_mul_of_nonneg_left hfour (pow_nonneg (Real.log_pos one_lt_two).le k))

end Erdos446
