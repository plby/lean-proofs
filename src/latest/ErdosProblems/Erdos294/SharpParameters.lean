/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos297.GoodSetDensity
import ErdosProblems.Erdos297.SupplyNumerics
import ErdosProblems.Erdos297.AuxiliarySupply

/-!
# Corrected constant-width parameters for Erdős Problem 294

The auxiliary-prime averaging in Liu--Sawhney Proposition 3.2 costs one
additional `log log` factor compared with the displayed cutoff in the paper.
At the local scale this loss is harmless for Theorem 1.6: it becomes one
additional power of `log log log` in the final bound.  We use the deliberately
generous cutoff

`S = N / (10^40 (log N)^3 (log log N)^9)`.

The factorization cutoff is the already verified safe cutoff from the 297
development.  Keeping it unchanged lets all finite sieve and Fourier lemmas
be reused without altering that development.
-/

open Filter Finset Real
open scoped Topology

namespace Erdos294.SharpParameters

open Erdos297
open Erdos297.GoodFactorization

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A fixed amount of room for every rounding and sieve constant. -/
def sharpConstant : ℝ := (10 : ℝ) ^ 40

lemma sharpConstant_pos : 0 < sharpConstant := by
  norm_num [sharpConstant]

/-- Corrected prime-power cutoff at the constant-width scale. -/
def sharpSReal (N : ℕ) : ℝ :=
  (N : ℝ) /
    (sharpConstant * logScale N ^ 3 * logLogScale N ^ 9)

noncomputable def sharpS (N : ℕ) : ℕ := ⌊sharpSReal N⌋₊

/-- A constant-width lower endpoint.  The factor `100` retains enough of
the density-`0.89` source set for reciprocal mass strictly larger than two. -/
def sharpM (N : ℕ) : ℕ := N / 100

/-- The full structured denominator set used by the prescribed local limit. -/
def sharpGoodSet (N : ℕ) : Finset ℕ :=
  goodDenominators N (sharpM N) (sharpS N)

lemma sharpGoodSet_subset_Icc (N : ℕ) :
    sharpGoodSet N ⊆ Icc (sharpM N) N :=
  goodDenominators_subset_Icc _ _ _

lemma sharpGoodSet_pos {N n : ℕ} (hM : 1 ≤ sharpM N)
    (hn : n ∈ sharpGoodSet N) : 0 < n :=
  goodDenominator_pos hM hn

lemma eventually_two_mul_SReal_le_sharpSReal :
    ∀ᶠ N : ℕ in atTop, 2 * Erdos297.SReal N ≤ sharpSReal N := by
  filter_upwards
    [ Erdos297.eventually_logLog_pow_nine_le_logScale
        (2 * sharpConstant) (mul_pos (by norm_num) sharpConstant_pos)
    , eventually_pos_scales ] with N hslow hpos
  rcases hpos with ⟨hN, hLone, hLLone, hLLL⟩
  have hL : 0 < logScale N := zero_lt_one.trans hLone
  have hLL : 0 < logLogScale N := zero_lt_one.trans hLLone
  dsimp [Erdos297.SReal, sharpSReal]
  field_simp
  have hquot : 2 * logLogScale N ^ 9 ≤
      logScale N / sharpConstant := by
    rw [le_div_iff₀ sharpConstant_pos]
    calc
      2 * logLogScale N ^ 9 * sharpConstant =
          2 * sharpConstant * logLogScale N ^ 9 := by ring
      _ ≤ logScale N := hslow
  nlinarith

lemma eventually_sharpSReal_ge_two :
    ∀ᶠ N : ℕ in atTop, 2 ≤ sharpSReal N := by
  filter_upwards [eventually_real_scales_ge_two,
      eventually_two_mul_SReal_le_sharpSReal] with N hscales hcompare
  calc
    2 ≤ Erdos297.SReal N := hscales.1
    _ ≤ 2 * Erdos297.SReal N := by nlinarith
    _ ≤ sharpSReal N := hcompare

/-- The old `N/log^4 N` cutoff is eventually smaller than the corrected
constant-width cutoff.  This transfers all density estimates. -/
lemma eventually_S_le_sharpS :
    ∀ᶠ N : ℕ in atTop, Erdos297.S N ≤ sharpS N := by
  filter_upwards [eventually_two_mul_SReal_le_sharpSReal,
      eventually_sharpSReal_ge_two, eventually_pos_scales] with
      N hcompare htwo hpos
  have hOld : (Erdos297.S N : ℝ) ≤
      Erdos297.SReal N := by
    apply Nat.floor_le
    dsimp [Erdos297.SReal]
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith [hpos.2.1]) _)
  have hhalf : Erdos297.SReal N ≤ sharpSReal N / 2 := by
    linarith
  have hfloor : sharpSReal N / 2 ≤ (sharpS N : ℝ) :=
    Erdos297.half_le_floor htwo
  exact_mod_cast hOld.trans (hhalf.trans hfloor)

lemma tendsto_sharpS_atTop : Tendsto sharpS atTop atTop := by
  exact tendsto_atTop_mono' atTop eventually_S_le_sharpS
    Erdos297.SupplyNumerics.tendsto_S_atTop

lemma eventually_two_hundred_le_sharpS :
    ∀ᶠ N : ℕ in atTop, 200 ≤ sharpS N :=
  tendsto_sharpS_atTop.eventually_ge_atTop 200

lemma eventually_smallPrimeCutoff_le_sharpS :
    ∀ᶠ N : ℕ in atTop,
      Erdos297.SupplyNumerics.smallPrimeCutoff N ≤ sharpS N := by
  filter_upwards
    [ Erdos297.SupplyNumerics.eventually_smallPrimeCutoff_le_S
    , eventually_S_le_sharpS ] with N hX hS
  exact hX.trans hS

lemma eventually_auxiliaryPrime_le_sharpS :
    ∀ᶠ N : ℕ in atTop, ∀ p ∈ Erdos297.PrimeIntervals.auxiliaryPrimes N,
      p ≤ sharpS N := by
  filter_upwards
    [ Erdos297.AuxiliarySupply.eventually_auxiliaryPrime_le_S
    , eventually_S_le_sharpS ] with N hp hS p hpP
  exact (hp p hpP).trans hS

lemma eventually_hundred_mul_KSafe_le_sharpS_sq :
    ∀ᶠ N : ℕ in atTop, 100 * KSafe N ≤ (sharpS N) ^ 2 := by
  filter_upwards
    [ Erdos297.SupplyNumerics.eventually_hundred_mul_KSafe_le_S_sq
    , eventually_S_le_sharpS ] with N hquad hS
  exact hquad.trans (Nat.pow_le_pow_left hS 2)

lemma eventually_N_div_KSafe_le_sharpS :
    ∀ᶠ N : ℕ in atTop, N / KSafe N ≤ sharpS N := by
  filter_upwards
    [ Erdos297.eventually_N_div_KSafe_le_S
    , eventually_S_le_sharpS ] with N hdiv hS
  exact hdiv.trans hS

lemma eventually_sharpS_le_KSafe :
    ∀ᶠ N : ℕ in atTop, sharpS N ≤ KSafe N := by
  filter_upwards [eventually_pos_scales, eventually_sharpSReal_ge_two,
      Erdos297.eventually_KSafeReal_ge_two] with
      N hpos hSlarge hKlarge
  rcases hpos with ⟨hN, hLone, hLLone, hLLL⟩
  have hL : 0 < logScale N := zero_lt_one.trans hLone
  have hLL : 0 < logLogScale N := zero_lt_one.trans hLLone
  have hSfloor : (sharpS N : ℝ) ≤ sharpSReal N :=
    Nat.floor_le (by
      dsimp [sharpSReal]
      exact div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (mul_nonneg sharpConstant_pos.le (pow_nonneg hL.le _))
          (pow_nonneg hLL.le _)))
  have hKhalf : KSafeReal N / 2 ≤ (KSafe N : ℝ) :=
    Erdos297.half_le_floor hKlarge
  have hreal : sharpSReal N ≤ KSafeReal N / 2 := by
    dsimp [sharpSReal, KSafeReal, KReal]
    have hcoeff : 2 * (10 : ℝ) ^ 7 ≤ sharpConstant * logScale N ^ 2 *
        logLogScale N ^ 8 := by
      have hL2 : 1 ≤ logScale N ^ 2 := one_le_pow₀ hLone.le
      have hLL8 : 1 ≤ logLogScale N ^ 8 := one_le_pow₀ hLLone.le
      calc
        2 * (10 : ℝ) ^ 7 ≤ sharpConstant := by norm_num [sharpConstant]
        _ ≤ sharpConstant * logScale N ^ 2 :=
          le_mul_of_one_le_right sharpConstant_pos.le hL2
        _ ≤ sharpConstant * logScale N ^ 2 * logLogScale N ^ 8 :=
          le_mul_of_one_le_right (mul_nonneg sharpConstant_pos.le (sq_nonneg _)) hLL8
    have hcoeff' : 2 * (10 : ℝ) ^ 7 / sharpConstant ≤
        logScale N ^ 2 * logLogScale N ^ 8 := by
      rw [div_le_iff₀ sharpConstant_pos]
      calc
        2 * (10 : ℝ) ^ 7 ≤
            sharpConstant * logScale N ^ 2 * logLogScale N ^ 8 := hcoeff
        _ = logScale N ^ 2 * logLogScale N ^ 8 * sharpConstant := by ring
    field_simp
    linarith
  exact_mod_cast hSfloor.trans (hreal.trans hKhalf)

end

end Erdos294.SharpParameters
