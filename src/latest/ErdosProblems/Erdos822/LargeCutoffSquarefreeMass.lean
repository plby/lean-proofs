/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.LargeCutoffB4
import ErdosProblems.Erdos822.LargeGcdFreeFilter
import ErdosProblems.Erdos822.PrimeReciprocalUpper

/-!
# Squarefree mass at the concrete B4 cutoff

The B4 layer at cutoff N^4 has logarithmic reciprocal mass.  The global
prime-square estimate removes only a bounded amount at the same cutoff, so
the corrected squarefree B4 layer still has logarithmic mass.
-/

namespace Erdos822

open scoped BigOperators

/-- The explicit prime-square loss at y=N^4 is uniformly bounded once the
middle-prime reciprocal interval has reached its eventual upper bound. -/
theorem largeCutoff_squarefree_error_le_three
    {N : ℕ} (hN : 2 ≤ N)
    (hR :
      ∑ r ∈ middlePrimes N, (1 : ℝ) / r ≤ 1) :
    (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          ((((1 : ℝ) / (N ^ 4 : ℕ)) +
              ((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) *
            (harmonic N : ℝ)) ≤ 3 := by
  have hK :
      ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k ≤ (N : ℝ) := by
    exact (sum_inv_oddSmallFactors_le_harmonic N).trans
      (harmonic_le_natCast N)
  have hH : (harmonic N : ℝ) ≤ (N : ℝ) :=
    harmonic_le_natCast N
  have hK0 : 0 ≤ ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k :=
    Finset.sum_nonneg fun k hk => by positivity
  have hR0 : 0 ≤ ∑ r ∈ middlePrimes N, (1 : ℝ) / r :=
    Finset.sum_nonneg fun r hr => by positivity
  have hH0 : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity
  have hfirst :
      (N : ℝ) * (1 * (((1 : ℝ) / (N ^ 4 : ℕ)) * (N : ℝ))) ≤ 1 := by
    have hpow : N ^ 2 ≤ N ^ 4 :=
      Nat.pow_le_pow_right (by omega : 1 ≤ N) (by omega)
    have hpowR : ((N ^ 2 : ℕ) : ℝ) ≤ ((N ^ 4 : ℕ) : ℝ) := by
      exact_mod_cast hpow
    have hden : (0 : ℝ) < ((N ^ 4 : ℕ) : ℝ) := by positivity
    calc
      (N : ℝ) * (1 * (((1 : ℝ) / (N ^ 4 : ℕ)) * (N : ℝ))) =
          ((N ^ 2 : ℕ) : ℝ) / ((N ^ 4 : ℕ) : ℝ) := by
        push_cast
        ring
      _ ≤ 1 := by
        apply (div_le_iff₀ hden).2
        simpa only [one_mul] using hpowR
  have hsecond :
      (N : ℝ) *
        (1 * ((((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) *
          (N : ℝ))) ≤ 2 := by
    have hpow : N ^ 16 ≤ N ^ 21 :=
      Nat.pow_le_pow_right (by omega : 1 ≤ N) (by omega)
    have hpowR : ((N ^ 16 : ℕ) : ℝ) ≤ ((N ^ 21 : ℕ) : ℝ) := by
      exact_mod_cast hpow
    have hden : (0 : ℝ) < ((N ^ 21 : ℕ) : ℝ) := by positivity
    calc
      (N : ℝ) *
          (1 * ((((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) *
            (N : ℝ))) =
          2 * (((N ^ 16 : ℕ) : ℝ) / ((N ^ 21 : ℕ) : ℝ)) := by
        push_cast
        ring
      _ ≤ 2 * 1 := by
        apply mul_le_mul_of_nonneg_left
        · apply (div_le_iff₀ hden).2
          simpa only [one_mul] using hpowR
        · norm_num
      _ = 2 := by ring
  calc
    (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          ((((1 : ℝ) / (N ^ 4 : ℕ)) +
              ((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) *
            (harmonic N : ℝ)) ≤
        (N : ℝ) * 1 *
          ((((1 : ℝ) / (N ^ 4 : ℕ)) +
              ((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) *
            (N : ℝ)) := by
      gcongr
    _ =
        (N : ℝ) * (1 * (((1 : ℝ) / (N ^ 4 : ℕ)) * (N : ℝ))) +
          (N : ℝ) *
            (1 * ((((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) *
              (N : ℝ))) := by ring
    _ ≤ 3 := by linarith

/-- The corrected B4 family at cutoff N^4 retains logarithmic reciprocal
mass after removing repeated large shifted prime factors. -/
theorem eventually_squarefreeLargeGcdFree_pow_four_log_mass :
    ∀ᶠ N : ℕ in Filter.atTop,
      (1 / 8000 : ℝ) * Real.log (N : ℝ) ≤
        ∑ m ∈ squarefreeLargeGcdFreeOddCofactors N (N ^ 4),
          (1 : ℝ) / m := by
  have hlog :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (24000 : ℝ))
  filter_upwards [eventually_largeCutoffGoodOddCofactors_log_mass,
      eventually_reciprocalPrimeIntervalSum_four_five_upper_one,
      hlog, Filter.eventually_ge_atTop 2] with N hraw hR hlogN hN
  change (24000 : ℝ) ≤ Real.log (N : ℝ) at hlogN
  have hR' :
      ∑ r ∈ middlePrimes N, (1 : ℝ) / r ≤ 1 := by
    simpa [reciprocalPrimeIntervalSum, middlePrimes_eq_primesLE_sdiff]
      using hR
  have hraw' :
      (1 / 4000 : ℝ) * Real.log (N : ℝ) ≤
        ∑ m ∈ largeGcdFreeOddCofactors N (N ^ 4),
          (1 : ℝ) / m := by
    rw [← largeCutoffGoodOddCofactors_eq_largeGcdFree]
    exact hraw
  have hy1 : 1 ≤ N ^ 4 := one_le_pow₀ (by omega)
  have hyN : N ^ 4 < N ^ 21 :=
    Nat.pow_lt_pow_right (by omega : 1 < N) (by omega)
  have hret := sum_inv_largeSquarefree_largeGcdFree_ge
    (N := N) (y := N ^ 4)
    hN hy1 hyN hraw'
    (largeCutoff_squarefree_error_le_three hN hR')
  calc
    (1 / 8000 : ℝ) * Real.log (N : ℝ) ≤
        (1 / 4000 : ℝ) * Real.log (N : ℝ) - 3 := by
      nlinarith
    _ ≤ ∑ m ∈ squarefreeLargeGcdFreeOddCofactors N (N ^ 4),
          (1 : ℝ) / m := by
      simpa [squarefreeLargeGcdFreeOddCofactors] using hret

end Erdos822
