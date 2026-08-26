/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SlowCutoffB4RetainedMass
import ErdosProblems.Erdos822.LargeGcdFreeFilter

/-!
# Squarefree shifted coefficients at the slow B4 cutoff
-/

namespace Erdos822

open scoped BigOperators

/-- The global repeated-prime correction is bounded by the same cubic
logarithmic envelope at the slow cutoff. -/
theorem slowCutoff_squarefree_error_le_three
    {N y : ℕ} (hN : 2 ≤ N) (hy : 1 ≤ y) (hyN : y ≤ N)
    (hR : ∑ r ∈ middlePrimes N, (1 : ℝ) / r ≤ 1)
    (henv : (1 + Real.log (N : ℝ)) ^ 3 / (y : ℝ) ≤ 1) :
    (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          ((((1 : ℝ) / y) +
              ((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) *
            (harmonic N : ℝ)) ≤ 3 := by
  let A : ℝ := 1 + Real.log (N : ℝ)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    have hlog : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    linarith
  have hA1 : 1 ≤ A := by
    dsimp [A]
    have hlog : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    linarith
  have hK :
      ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k ≤ A :=
    (sum_inv_oddSmallFactors_le_harmonic N).trans
      (by simpa [A] using harmonic_le_one_add_log N)
  have hH : (harmonic N : ℝ) ≤ A := by
    simpa [A] using harmonic_le_one_add_log N
  have hK0 : 0 ≤ ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k :=
    Finset.sum_nonneg fun k hk => by positivity
  have hR0 : 0 ≤ ∑ r ∈ middlePrimes N, (1 : ℝ) / r :=
    Finset.sum_nonneg fun r hr => by positivity
  have hH0 : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity
  have hyR : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hN21R : (0 : ℝ) < ((N ^ 21 : ℕ) : ℝ) := by positivity
  have hpow : y * N ^ 14 ≤ N ^ 21 := by
    calc
      y * N ^ 14 ≤ N * N ^ 14 := Nat.mul_le_mul_right (N ^ 14) hyN
      _ = N ^ 15 := by ring
      _ ≤ N ^ 21 := Nat.pow_le_pow_right (by omega : 1 ≤ N) (by omega)
  have hratio :
      (((N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) ≤ (1 : ℝ) / y := by
    apply (div_le_div_iff₀ hN21R hyR).2
    norm_num
    exact_mod_cast (by simpa [Nat.mul_comm] using hpow)
  have htwoRatio :
      (((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) ≤
        (2 : ℝ) / y := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    calc
      (2 : ℝ) * (N ^ 14 : ℕ) / (N ^ 21 : ℕ) =
          2 * (((N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) := by ring
      _ ≤ 2 * ((1 : ℝ) / y) := mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = (2 : ℝ) / y := by ring
  have hA2A3 : A ^ 2 ≤ A ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hA1 (sq_nonneg A)
    simpa [pow_two, pow_succ] using h
  calc
    (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
          ((((1 : ℝ) / y) +
              ((2 * N ^ 14 : ℕ) : ℝ) / (N ^ 21 : ℕ)) *
            (harmonic N : ℝ)) ≤
        A * 1 * ((((1 : ℝ) / y) + (2 : ℝ) / y) * A) := by
      gcongr
    _ = 3 * A ^ 2 / (y : ℝ) := by ring
    _ ≤ 3 * A ^ 3 / (y : ℝ) := by gcongr
    _ = 3 * (A ^ 3 / (y : ℝ)) := by ring
    _ ≤ 3 * 1 := mul_le_mul_of_nonneg_left (by simpa [A] using henv) (by norm_num)
    _ = 3 := by ring

/-- The slow-B4 family remains logarithmically large after imposing the
large-prime squarefree condition on its shifted coefficient. -/
theorem eventually_slowSquarefreeLargeGcdFree_log_mass
    {S : ℕ} (hS : 0 < S) :
    ∀ᶠ N : ℕ in Filter.atTop,
      let y := Nat.nthRoot (4 * S) N
      (1 / 8000 : ℝ) * Real.log (N : ℝ) ≤
        ∑ m ∈ squarefreeLargeGcdFreeOddCofactors N y, (1 : ℝ) / m := by
  have hlog :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (24000 : ℝ))
  filter_upwards [eventually_slowLargeGcdFree_log_mass hS,
      eventually_reciprocalPrimeIntervalSum_four_five_upper_one,
      eventually_slowCutoff_log_cube_div_le_one hS,
      eventually_nthRoot_ge (4 * S) 1 (by omega), hlog,
      Filter.eventually_ge_atTop 2] with N hraw hR henv hy hlogN hN
  let y := Nat.nthRoot (4 * S) N
  have hy1 : 1 ≤ y := by simpa [y] using hy
  have hyN : y ≤ N := by
    dsimp [y]
    exact nthRoot_le_self_of_pos (by omega)
  have hyN21 : y < N ^ 21 :=
    hyN.trans_lt (by
      have := Nat.pow_lt_pow_right (show 1 < N by omega) (show 1 < 21 by omega)
      simpa using this)
  have hR' : ∑ r ∈ middlePrimes N, (1 : ℝ) / r ≤ 1 := by
    simpa [reciprocalPrimeIntervalSum, middlePrimes_eq_primesLE_sdiff] using hR
  have henv' : (1 + Real.log (N : ℝ)) ^ 3 / (y : ℝ) ≤ 1 := by
    simpa [y] using henv
  have hraw' :
      (1 / 4000 : ℝ) * Real.log (N : ℝ) ≤
        ∑ m ∈ largeGcdFreeOddCofactors N y, (1 : ℝ) / m := by
    simpa [y] using hraw
  have hret := sum_inv_largeSquarefree_largeGcdFree_ge
    (N := N) (y := y) hN hy1 hyN21 hraw'
      (slowCutoff_squarefree_error_le_three hN hy1 hyN hR' henv')
  change (24000 : ℝ) ≤ Real.log (N : ℝ) at hlogN
  calc
    (1 / 8000 : ℝ) * Real.log (N : ℝ) ≤
        (1 / 4000 : ℝ) * Real.log (N : ℝ) - 3 := by
      nlinarith
    _ ≤ ∑ m ∈ squarefreeLargeGcdFreeOddCofactors N y,
          (1 : ℝ) / m := by
      simpa [squarefreeLargeGcdFreeOddCofactors] using hret

end Erdos822
