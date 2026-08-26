/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.HarmonicElementary
import ErdosProblems.Erdos822.PrimeSquareMass

/-!
# Crude harmonic bounds for remainder absorption

The beta remainder only needs a very coarse estimate.  Bounding every
harmonic summand by one gives H_N <= N, which combines with the slow-cutoff
power inequality to dominate the remainder by the inverse-prime scale.
-/

namespace Erdos822

open scoped BigOperators

/-- The square beta remainder at the slow cutoff, multiplied by a sieve
prime and one harmonic factor, is at most the large-layer denominator. -/
theorem slowSieveCutoff_prime_mul_error_mul_harmonic_le
    {N S p : ℕ} (hN : 2 ≤ N) (hS : 0 < S)
    (hp : p ≤ Nat.nthRoot (4 * S) N) :
    (p : ℝ) *
        (((Nat.nthRoot (4 * S) N ^ S : ℕ) : ℝ) ^ 2) *
          (harmonic N : ℝ) ≤
      ((N ^ 21 : ℕ) : ℝ) := by
  let y := Nat.nthRoot (4 * S) N
  have hyN : y ≤ N := by
    dsimp [y]
    exact nthRoot_le_self_of_pos (by omega)
  have herrorNat :
      (Nat.nthRoot (4 * S) N ^ S) ^ 2 ≤ N :=
    slowSieveCutoff_error_sq_le N S hS
  have herror :
      (((Nat.nthRoot (4 * S) N ^ S : ℕ) : ℝ) ^ 2) ≤
        (N : ℝ) := by
    exact_mod_cast herrorNat
  have hH : (harmonic N : ℝ) ≤ (N : ℝ) :=
    harmonic_le_natCast N
  have hH0 : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun i hi => by positivity
  have hpN : p ≤ N := hp.trans hyN
  have hpR : (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpN
  have hpowNat : N ^ 3 ≤ N ^ 21 :=
    Nat.pow_le_pow_right (by omega : 1 ≤ N) (by omega)
  calc
    (p : ℝ) *
        (((Nat.nthRoot (4 * S) N ^ S : ℕ) : ℝ) ^ 2) *
          (harmonic N : ℝ) ≤
        (N : ℝ) * (N : ℝ) * (N : ℝ) := by
      gcongr
    _ = ((N ^ 3 : ℕ) : ℝ) := by
      push_cast
      ring
    _ ≤ ((N ^ 21 : ℕ) : ℝ) := by
      exact_mod_cast hpowNat

end Erdos822
