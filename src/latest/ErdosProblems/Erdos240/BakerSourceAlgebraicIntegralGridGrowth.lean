/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAlgebraicTargetError
import ErdosProblems.Erdos240.BakerSourcePositiveStageGrowth

/-!
# Source-faithful algebraic bounds on the integral Lemma-4 grid

The old interpolation rows use the full level budget `Slevel`, rather than
the smaller boundary budget.  This file retains the exact level scaling and
closes the algebraic growth and perturbation-amplification estimates on the
whole disk of radius `3 * lemmaFourRadius N (t+1)`.  It then packages the
pointwise three-quarter row error and its comparison with the integral
Liouville threshold.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceAlgebraicIntegralGridGrowth

open Erdos240
open BakerLemma2Concrete
open BakerLemma3
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerLemma4InnerInduction
open BakerSourceAlgebraicMajorant
open BakerSourceAlgebraicMomentBounds
open BakerSourceAlgebraicStaticFactors
open BakerSourceAlgebraicTargetError
open BakerSourceAlgebraicUniformBounds
open BakerSourceMajorantClosedForm
open BakerSourcePositiveStageGrowth
open BakerSourceState
open BakerSourceUniformConstantCompletion

/-- The full level budget costs at most two source-height units in the
factorial-sensitive `(2B)^S` factor. -/
theorem fullLevel_oldDeltaPower_le_exp_two {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) (N : ℕ) :
    (((2 * P.Bsrc : ℕ) : ℝ) ^ P.Slevel N) ≤
      Real.exp (2 * sourceHeightUnit P) := by
  have hBpos : 0 < P.Bsrc := by
    have : (0 : ℝ) < P.Bsrc :=
      (Real.exp_pos 2).trans_le P.Bsrc_lower
    exact_mod_cast this
  apply VDPLParameters.pow_le_exp_of_mul_log_le (by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2) hBpos)
  have hS := P.Slevel_cast_le N
  have hlog := log_two_mul_Bsrc_le_two_h P
  have hlog0 : 0 ≤ Real.log (((2 * P.Bsrc : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    have hB : 1 ≤ P.Bsrc := by
      have hBreal : (1 : ℝ) ≤ P.Bsrc :=
        (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans P.Bsrc_lower
      exact_mod_cast hBreal
    exact_mod_cast (show 1 ≤ 2 * P.Bsrc by omega)
  have hlog' : Real.log (((2 * P.Bsrc : ℕ) : ℝ)) ≤ 2 * P.h := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlog
  have hq : P.qInvPow N ≤ 1 := by
    have h := P.qInvPow_antitone (Nat.zero_le N)
    simpa [VDPLParameters.qInvPow] using h
  have hcore : 0 ≤ P.k * P.Omega * Real.log P.OmegaOld :=
    mul_nonneg (mul_nonneg P.k_pos.le P.Omega_pos.le)
      P.log_OmegaOld_pos.le
  have hscale : P.levelScale N ≤
      P.k * P.Omega * Real.log P.OmegaOld := by
    unfold VDPLParameters.levelScale
    calc
      P.qInvPow N * P.k * P.Omega * Real.log P.OmegaOld =
          P.qInvPow N *
            (P.k * P.Omega * Real.log P.OmegaOld) := by ring
      _ ≤ 1 * (P.k * P.Omega * Real.log P.OmegaOld) :=
        mul_le_mul_of_nonneg_right hq hcore
      _ = P.k * P.Omega * Real.log P.OmegaOld := by ring
  calc
    (P.Slevel N : ℝ) * Real.log (((2 * P.Bsrc : ℕ) : ℝ)) ≤
        P.levelScale N * (2 * P.h) :=
      mul_le_mul hS hlog' hlog0 (P.levelScale_pos N).le
    _ ≤ (P.k * P.Omega * Real.log P.OmegaOld) * (2 * P.h) := by
      gcongr
    _ = 2 * sourceHeightUnit P := by
      unfold sourceHeightUnit
      ring

/-- Norm monotonicity of the scaled head argument. -/
theorem norm_scaledArgument_mono {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) {z w : ℂ}
    (hzw : ‖z‖ ≤ ‖w‖) :
    ‖scaledArgument P.q N z‖ ≤ ‖scaledArgument P.q N w‖ := by
  unfold scaledArgument
  rw [norm_div, norm_div]
  exact div_le_div_of_nonneg_right hzw (norm_nonneg _)

/-- The powered head-Delta envelope is monotone in the norm of its
evaluation point. -/
theorem sourceHeadDeltaMajorant_mono_norm {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (N : ℕ) {z w : ℂ}
    (hzw : ‖z‖ ≤ ‖w‖) :
    sourceHeadDeltaMajorant P N z ≤ sourceHeadDeltaMajorant P N w := by
  unfold sourceHeadDeltaMajorant
  have hscaled := norm_scaledArgument_mono P N hzw
  have hceil :
      Nat.ceil (‖scaledArgument P.q N z‖ + P.h) ≤
        Nat.ceil (‖scaledArgument P.q N w‖ + P.h) :=
    Nat.ceil_mono (add_le_add_left hscaled P.h)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (Nat.mul_le_mul_right P.LzeroPlusOne
      (Nat.add_le_add_right (Nat.add_le_add_right hceil 1) P.h))

/-- The positive-contour head estimate also bounds every point in the
enclosed disk. -/
theorem sourceHeadDeltaMajorant_le_exp_eight_positiveStageHeightUnit_of_le
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (N t : ℕ) (z : ℂ)
    (hz : ‖z‖ ≤ 3 * P.lemmaFourRadius N (t + 1)) :
    sourceHeadDeltaMajorant P N z ≤
      Real.exp (8 * positiveStageHeightUnit P t) := by
  let w : ℂ := (3 * (P.lemmaFourRadius N (t + 1) : ℝ) : ℝ)
  have hw : ‖w‖ = 3 * P.lemmaFourRadius N (t + 1) := by
    dsimp only [w]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  exact (sourceHeadDeltaMajorant_mono_norm P N (hz.trans_eq hw.symm)).trans
    (sourceHeadDeltaMajorant_le_exp_eight_positiveStageHeightUnit
      P N t w hw)

/-- The level-scaled algebraic exponential estimate also bounds the whole
positive-stage disk. -/
theorem algebraicRateExponent_le_six_positiveStageHeightUnit_of_le
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (N t : ℕ) (z : ℂ)
    (hz : ‖z‖ ≤ 3 * P.lemmaFourRadius N (t + 1)) :
    P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖ ≤
      6 * positiveStageHeightUnit P t := by
  let w : ℂ := (3 * (P.lemmaFourRadius N (t + 1) : ℝ) : ℝ)
  have hw : ‖w‖ = 3 * P.lemmaFourRadius N (t + 1) := by
    dsimp only [w]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  have hcoeff : 0 ≤ P.qInvPow N * sourceAlgebraicRateBound P :=
    mul_nonneg (P.qInvPow_pos N).le (sourceAlgebraicRateBound_nonneg P)
  exact (mul_le_mul_of_nonneg_left (hz.trans_eq hw.symm) hcoeff).trans
    (algebraicRateExponent_le_six_positiveStageHeightUnit P N t w hw)

/-- Up to the terminal Lemma-4 stage, a positive-stage unit is bounded by
`sqrt(k)` times the fixed source-height unit. -/
theorem positiveStageHeightUnit_le_sqrt_mul_sourceHeightUnit
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {t : ℕ}
    (ht : t < terminalStage P) :
    positiveStageHeightUnit P t ≤
      P.k ^ (1 / 2 : ℝ) * sourceHeightUnit P := by
  have htcast : ((t + 1 : ℕ) : ℝ) ≤ 3 * (P.rank + 1 : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr ht)
  have heps : P.epsilon * ((t + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
    rw [P.epsilon_eq]
    have hrank : (0 : ℝ) < P.rank + 1 := by positivity
    field_simp
    nlinarith
  have hexp :
      1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ) ≤ 3 / 2 := by
    nlinarith [P.sigma_pos]
  have hkpow :
      P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ)) ≤
        P.k ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le P.one_le_k hexp
  have hkthree : P.k ^ (3 / 2 : ℝ) = P.k ^ (1 / 2 : ℝ) * P.k := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by ring,
      Real.rpow_add P.k_pos, Real.rpow_one]
  unfold positiveStageHeightUnit sourceHeightUnit
  rw [hkthree] at hkpow
  have hrest : 0 ≤ (P.h : ℝ) * P.Omega * Real.log P.OmegaOld := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg P.h) P.Omega_pos.le)
      P.log_OmegaOld_pos.le
  have hmul := mul_le_mul_of_nonneg_left hkpow hrest
  nlinarith

/-- The entire full-budget disk-growth ledger lies below the structural
quarter exponent used by the algebraic comparison theorem. -/
theorem three_height_add_fifteen_stage_le_structural_quarter
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {t : ℕ}
    (ht : t < terminalStage P) :
    3 * sourceHeightUnit P + 15 * positiveStageHeightUnit P t ≤
      sourceExponent P (P.C * Real.log P.OmegaOld) / 4 := by
  let H : ℝ := sourceHeightUnit P
  let T : ℝ := positiveStageHeightUnit P t
  let u : ℝ := P.k ^ (1 / 2 : ℝ)
  have hT : T ≤ u * H := by
    simpa only [T, u, H] using
      positiveStageHeightUnit_le_sqrt_mul_sourceHeightUnit P ht
  have hu : (64 : ℝ) ≤ u := by
    simpa only [u] using P.sixtyFour_le_k_rpow_half
  have hu0 : 0 ≤ u := (by positivity : 0 ≤ P.k ^ (1 / 2 : ℝ))
  have hu2 : u * u = P.k := by
    dsimp only [u]
    rw [← Real.rpow_add P.k_pos]
    norm_num
  have hcoeff : 3 + 15 * u ≤ P.k / 4 := by
    nlinarith
  have hH : 0 ≤ H := (sourceHeightUnit_pos P).le
  have hfirst : 3 * H + 15 * T ≤ P.k * H / 4 := by
    calc
      3 * H + 15 * T ≤ (3 + 15 * u) * H := by
        nlinarith
      _ ≤ (P.k / 4) * H :=
        mul_le_mul_of_nonneg_right hcoeff hH
      _ = P.k * H / 4 := by ring
  have hC : P.C = P.k ^ 2 := by
    unfold VDPLParameters.C
    rw [P.mu_eq]
    norm_num [Real.rpow_two]
  have hlog := P.h_cast_le_log_Bsrc
  have hrest : 0 ≤ P.k ^ 2 * P.Omega * Real.log P.OmegaOld := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg P.k) P.Omega_pos.le)
      P.log_OmegaOld_pos.le
  have hmul := mul_le_mul_of_nonneg_left hlog hrest
  have hkH : P.k * H ≤
      sourceExponent P (P.C * Real.log P.OmegaOld) := by
    calc
      P.k * H = P.k ^ 2 * P.Omega * Real.log P.OmegaOld * P.h := by
        dsimp only [H, sourceHeightUnit]
        ring
      _ ≤ P.k ^ 2 * P.Omega * Real.log P.OmegaOld *
          Real.log P.Bsrc := hmul
      _ = sourceExponent P (P.C * Real.log P.OmegaOld) := by
        unfold sourceExponent VDPLParameters.Omega
        rw [hC]
        ring
  exact hfirst.trans (by nlinarith)

/-- Closed sharp algebraic growth on the full-budget integral disk. -/
theorem sourceSharpAlgebraicGrowthMajorant_le_integralDisk_structural_quarter
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    (N : ℕ) {t : ℕ} (ht : t < terminalStage P) (z : ℂ)
    (hz : ‖z‖ ≤ 3 * P.lemmaFourRadius N (t + 1)) :
    sourceSharpAlgebraicGrowthMajorant P N z (P.Slevel N) ≤
      Real.exp (sourceExponent P
        (P.C * Real.log P.OmegaOld) / 4) := by
  let H : ℝ := sourceHeightUnit P
  let T : ℝ := positiveStageHeightUnit P t
  have hstatic := support_sq_mul_coeffHeight_le_exp_two_thirds P hreq
  have hold := fullLevel_oldDeltaPower_le_exp_two P N
  have hside := oldDeltaSidePower_le_exp_positiveStageHeightUnit P N t
  have hhead :=
    sourceHeadDeltaMajorant_le_exp_eight_positiveStageHeightUnit_of_le
      P N t z hz
  have hrate :
      Real.exp (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖) ≤
        Real.exp (6 * T) := by
    apply Real.exp_le_exp.mpr
    simpa only [T] using
      algebraicRateExponent_le_six_positiveStageHeightUnit_of_le P N t z hz
  have hold0 : 0 ≤ (((2 * P.Bsrc : ℕ) : ℝ) ^ P.Slevel N) := by
    positivity
  have hhead0 : 0 ≤ sourceHeadDeltaMajorant P N z := by
    unfold sourceHeadDeltaMajorant
    positivity
  have hside0 : 0 ≤ (2 : ℝ) ^ levelOldDeltaSideSum P N := by positivity
  have hrate0 : 0 ≤ Real.exp
      (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖) :=
    (Real.exp_pos _).le
  have hstatic' :
      (initialSupportBound P : ℝ) *
          (P.coeffHeight * (initialSupportBound P : ℝ)) ≤
        Real.exp ((2 / 3 : ℝ) * H) := by
    simpa only [H, sourceHeightUnit] using hstatic
  have hold' : (((2 * P.Bsrc : ℕ) : ℝ) ^ P.Slevel N) ≤
      Real.exp (2 * H) := by
    simpa only [H] using hold
  have hhead' : sourceHeadDeltaMajorant P N z ≤ Real.exp (8 * T) := by
    simpa only [T] using hhead
  have hside' : (2 : ℝ) ^ levelOldDeltaSideSum P N ≤ Real.exp T := by
    simpa only [T] using hside
  have hoh : (((2 * P.Bsrc : ℕ) : ℝ) ^ P.Slevel N) *
        sourceHeadDeltaMajorant P N z ≤
      Real.exp (2 * H) * Real.exp (8 * T) :=
    mul_le_mul hold' hhead' hhead0 (Real.exp_pos _).le
  have hohd : ((((2 * P.Bsrc : ℕ) : ℝ) ^ P.Slevel N) *
          sourceHeadDeltaMajorant P N z) *
        (2 : ℝ) ^ levelOldDeltaSideSum P N ≤
      (Real.exp (2 * H) * Real.exp (8 * T)) * Real.exp T :=
    mul_le_mul hoh hside' hside0
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have hdynamic :
      (((((2 * P.Bsrc : ℕ) : ℝ) ^ P.Slevel N) *
          sourceHeadDeltaMajorant P N z) *
        (2 : ℝ) ^ levelOldDeltaSideSum P N) *
        Real.exp (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖) ≤
      ((Real.exp (2 * H) * Real.exp (8 * T)) * Real.exp T) *
        Real.exp (6 * T) :=
    mul_le_mul hohd hrate hrate0
      (mul_nonneg
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
        (Real.exp_pos _).le)
  unfold sourceSharpAlgebraicGrowthMajorant sourceSharpDeltaFactorMajorant
  calc
    (initialSupportBound P : ℝ) *
          (P.coeffHeight * ((initialSupportBound P : ℝ) *
            (sourceHeadDeltaMajorant P N z *
              (((2 * P.Bsrc : ℕ) : ℝ) ^ P.Slevel N *
                (2 : ℝ) ^ levelOldDeltaSideSum P N)))) *
        Real.exp (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖) =
      ((initialSupportBound P : ℝ) *
        (P.coeffHeight * (initialSupportBound P : ℝ))) *
        (((((2 * P.Bsrc : ℕ) : ℝ) ^ P.Slevel N) *
          sourceHeadDeltaMajorant P N z) *
          (2 : ℝ) ^ levelOldDeltaSideSum P N) *
        Real.exp (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖) := by
          ring
    _ ≤ Real.exp ((2 / 3 : ℝ) * H) *
        (((Real.exp (2 * H) * Real.exp (8 * T)) * Real.exp T) *
          Real.exp (6 * T)) := by
      calc
        ((initialSupportBound P : ℝ) *
              (P.coeffHeight * (initialSupportBound P : ℝ))) *
            (((((2 * P.Bsrc : ℕ) : ℝ) ^ P.Slevel N) *
              sourceHeadDeltaMajorant P N z) *
              (2 : ℝ) ^ levelOldDeltaSideSum P N) *
              Real.exp
                (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖) ≤
          Real.exp ((2 / 3 : ℝ) * H) *
            (((((2 * P.Bsrc : ℕ) : ℝ) ^ P.Slevel N) *
              sourceHeadDeltaMajorant P N z) *
              (2 : ℝ) ^ levelOldDeltaSideSum P N) *
              Real.exp
                (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hstatic'
              (mul_nonneg (mul_nonneg hold0 hhead0) hside0)) hrate0
        _ = Real.exp ((2 / 3 : ℝ) * H) *
            (((((2 * P.Bsrc : ℕ) : ℝ) ^ P.Slevel N) *
              sourceHeadDeltaMajorant P N z) *
              (2 : ℝ) ^ levelOldDeltaSideSum P N *
              Real.exp
                (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖)) := by
          ring
        _ ≤ Real.exp ((2 / 3 : ℝ) * H) *
            (((Real.exp (2 * H) * Real.exp (8 * T)) * Real.exp T) *
              Real.exp (6 * T)) :=
          mul_le_mul_of_nonneg_left hdynamic (Real.exp_pos _).le
    _ = Real.exp ((8 / 3 : ℝ) * H + 15 * T) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
        ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (3 * H + 15 * T) := by
      apply Real.exp_le_exp.mpr
      have hH : 0 ≤ H := (sourceHeightUnit_pos P).le
      linarith
    _ ≤ Real.exp (sourceExponent P
        (P.C * Real.log P.OmegaOld) / 4) := by
      apply Real.exp_le_exp.mpr
      simpa only [H, T] using
        three_height_add_fifteen_stage_le_structural_quarter P ht

/-- The scaled perturbation amplification is also below the structural
quarter exponent throughout the integral disk. -/
theorem scaledAmplificationClosedForm_le_integralDisk_structural_quarter
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    (N : ℕ) {t : ℕ} (ht : t < terminalStage P) (z : ℂ)
    (hz : ‖z‖ ≤ 3 * P.lemmaFourRadius N (t + 1)) :
    (initialSupportBound P : ℝ) *
        (P.qInvPow N * P.LlastZero) * ‖z‖ ≤
      Real.exp (sourceExponent P
        (P.C * Real.log P.OmegaOld) / 4) := by
  let H : ℝ := sourceHeightUnit P
  let T : ℝ := positiveStageHeightUnit P t
  have hscaled : ‖scaledArgument P.q N z‖ ≤
      48 * P.h * P.k ^ (P.epsilon * ((t + 1 : ℕ) : ℝ)) := by
    unfold scaledArgument
    rw [norm_div, norm_pow, Complex.norm_natCast]
    have hqpow : (0 : ℝ) < (P.q : ℝ) ^ N := by
      exact_mod_cast pow_pos (Nat.zero_lt_of_lt P.one_lt_q) N
    rw [div_le_iff₀ hqpow]
    have hR : (P.lemmaFourRadius N (t + 1) : ℝ) ≤
        P.lemmaFourRadiusScale N (t + 1) :=
      Nat.floor_le (P.lemmaFourRadiusScale_pos N (t + 1)).le
    calc
      ‖z‖ ≤ 3 * (P.lemmaFourRadius N (t + 1) : ℝ) := hz
      _ ≤ 3 * P.lemmaFourRadiusScale N (t + 1) := by gcongr
      _ = (48 * P.h *
          P.k ^ (P.epsilon * ((t + 1 : ℕ) : ℝ))) *
          (P.q : ℝ) ^ N := by
        unfold VDPLParameters.lemmaFourRadiusScale
        push_cast
        ring
  have hqz : P.qInvPow N * ‖z‖ ≤
      48 * P.h * P.k ^ (P.epsilon * ((t + 1 : ℕ) : ℝ)) := by
    have heq : P.qInvPow N * ‖z‖ = ‖scaledArgument P.q N z‖ := by
      unfold scaledArgument VDPLParameters.qInvPow
      rw [norm_div, norm_pow, Complex.norm_natCast, Nat.cast_pow]
      field_simp
    simpa only [heq] using hscaled
  have hL := P.LlastZero_cast_le
  have hmiddle :
      (P.qInvPow N * P.LlastZero) * ‖z‖ ≤ 6 * T := by
    have hfirst :
        (P.qInvPow N * P.LlastZero) * ‖z‖ ≤
          (48 * P.h * P.k ^
            (P.epsilon * ((t + 1 : ℕ) : ℝ))) * P.LlastZeroScale := by
      calc
        (P.qInvPow N * P.LlastZero) * ‖z‖ =
            (P.qInvPow N * ‖z‖) * P.LlastZero := by ring
        _ ≤ (48 * P.h * P.k ^
              (P.epsilon * ((t + 1 : ℕ) : ℝ))) * P.LlastZeroScale :=
          mul_le_mul hqz hL (Nat.cast_nonneg _)
            (mul_nonneg
              (mul_nonneg (by norm_num) (Nat.cast_nonneg P.h))
              (Real.rpow_nonneg P.k_pos.le _))
    refine hfirst.trans ?_
    have hrank : (1 : ℝ) ≤ P.rank := by exact_mod_cast P.one_le_rank
    have hlognew : (1 : ℝ) ≤ Real.log P.newHeight :=
      P.one_le_log_newHeight
    have hden : 0 < (8 * P.rank : ℝ) := by positivity
    have hnew : 0 < Real.log P.newHeight := P.log_newHeight_pos
    have hinv : (8 * (P.rank : ℝ))⁻¹ ≤
        Real.log P.newHeight / 8 := by
      rw [inv_le_iff_one_le_mul₀' hden]
      nlinarith
    let A : ℝ := P.k ^ (1 - P.sigma) * P.Omega *
      Real.log P.OmegaOld
    have hA0 : 0 ≤ A := by
      dsimp only [A]
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg P.k_pos.le _) P.Omega_pos.le)
        P.log_OmegaOld_pos.le
    have hscale : P.LlastZeroScale ≤ A / 8 := by
      unfold VDPLParameters.LlastZeroScale
      dsimp only [A]
      rw [div_le_iff₀ hnew]
      have hmul := mul_le_mul_of_nonneg_right hinv hA0
      nlinarith
    calc
      (48 * (P.h : ℝ) *
          P.k ^ (P.epsilon * ((t + 1 : ℕ) : ℝ))) *
          P.LlastZeroScale ≤
        (48 * (P.h : ℝ) *
          P.k ^ (P.epsilon * ((t + 1 : ℕ) : ℝ))) * (A / 8) :=
        mul_le_mul_of_nonneg_left hscale
          (mul_nonneg
            (mul_nonneg (by norm_num) (Nat.cast_nonneg P.h))
            (Real.rpow_nonneg P.k_pos.le _))
      _ = 6 * T := by
        dsimp only [A, T, positiveStageHeightUnit]
        rw [show 1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ) =
          P.epsilon * ((t + 1 : ℕ) : ℝ) + (1 - P.sigma) by ring,
          Real.rpow_add P.k_pos]
        ring
  have hs : (initialSupportBound P : ℝ) ≤ Real.exp (H / 6) := by
    convert initialSupportBound_le_exp_sixth P hreq using 1
    congr 1
    dsimp only [H, sourceHeightUnit]
    ring
  have hmiddleExp : 6 * T ≤ Real.exp (6 * T) := by
    exact (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
      (Real.add_one_le_exp (6 * T))
  have hclosed :
      (initialSupportBound P : ℝ) *
          ((P.qInvPow N * P.LlastZero) * ‖z‖) ≤
        Real.exp (H / 6 + 6 * T) := by
    calc
      (initialSupportBound P : ℝ) *
          ((P.qInvPow N * P.LlastZero) * ‖z‖) ≤
        Real.exp (H / 6) * Real.exp (6 * T) :=
          mul_le_mul hs (hmiddle.trans hmiddleExp)
            (mul_nonneg
              (mul_nonneg (P.qInvPow_pos N).le (Nat.cast_nonneg _))
              (norm_nonneg z))
            (Real.exp_pos _).le
      _ = Real.exp (H / 6 + 6 * T) := by rw [Real.exp_add]
  calc
    (initialSupportBound P : ℝ) *
        (P.qInvPow N * P.LlastZero) * ‖z‖ =
      (initialSupportBound P : ℝ) *
        ((P.qInvPow N * P.LlastZero) * ‖z‖) := by ring
    _ ≤ Real.exp (H / 6 + 6 * T) := hclosed
    _ ≤ Real.exp (3 * H + 15 * T) := by
      apply Real.exp_le_exp.mpr
      have hH : 0 ≤ H := (sourceHeightUnit_pos P).le
      have hT0 : 0 ≤ T := (positiveStageHeightUnit_pos P t).le
      linarith
    _ ≤ Real.exp (sourceExponent P
        (P.C * Real.log P.OmegaOld) / 4) := by
      apply Real.exp_le_exp.mpr
      simpa only [H, T] using
        three_height_add_fifteen_stage_le_structural_quarter P ht

/-- Pointwise three-quarter algebraic row error at every integral node in
the next Lemma-4 rectangle. -/
theorem levelAlgebraicSourceRowError_integralNode_le_three_quarters
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    {N : ℕ} (state : LevelState P N) (b : Fin oldRank → ℤ)
    {bLast : ℤ} (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    {t l : ℕ} (ht : t < terminalStage P)
    (hl : l ≤ P.lemmaFourRadius N (t + 1))
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Slevel N)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld)) :
    levelAlgebraicSourceRowError P state b bLast (l : ℂ)
        (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) m ≤
      Real.exp (-3 * sourceExponent P
        (C₀ * Real.log P.OmegaOld) / 4) := by
  have hz : ‖(l : ℂ)‖ ≤ 3 * P.lemmaFourRadius N (t + 1) := by
    rw [Complex.norm_natCast]
    exact_mod_cast (hl.trans (Nat.le_mul_of_pos_left _ (by norm_num)))
  apply levelAlgebraicSourceRowError_le_exp_neg_three_quarters_of_closedForm
    P state b hb hbLastBound hbLast (l : ℂ) m hm hstruct hE
  · exact sourceSharpAlgebraicGrowthMajorant_le_integralDisk_structural_quarter
      P hreq N ht (l : ℂ) hz
  · exact scaledAmplificationClosedForm_le_integralDisk_structural_quarter
      P hreq N ht (l : ℂ) hz

/-- At a newly reached integral target the preceding row-error envelope is
strictly below the exact integral Liouville threshold. -/
theorem levelAlgebraicSourceRowError_integralTarget_le_threshold
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    {N : ℕ} (hN : P.LevelOK N) (state : LevelState P N)
    (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    {t l : ℕ} (ht : t < terminalStage P)
    (hl : l ≤ P.lemmaFourRadius N (t + 1))
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Slevel N)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hintegral :
      16 * P.k * sourceIntegralDenominatorConstant P ≤ C₀) :
    levelAlgebraicSourceRowError P state b bLast (l : ℂ)
        (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) m ≤
      stateIntegralLiouvilleThreshold P N m := by
  exact (levelAlgebraicSourceRowError_integralNode_le_three_quarters
    P hreq state b hb hbLastBound hbLast ht hl m hm hstruct hE).trans
      (exp_neg_three_quarters_sourceExponent_lt_integralThreshold
        P hN m hm hintegral).le

end Erdos240.BakerSourceAlgebraicIntegralGridGrowth

#print axioms
  Erdos240.BakerSourceAlgebraicIntegralGridGrowth.sourceSharpAlgebraicGrowthMajorant_le_integralDisk_structural_quarter
#print axioms
  Erdos240.BakerSourceAlgebraicIntegralGridGrowth.scaledAmplificationClosedForm_le_integralDisk_structural_quarter
#print axioms
  Erdos240.BakerSourceAlgebraicIntegralGridGrowth.levelAlgebraicSourceRowError_integralNode_le_three_quarters
#print axioms
  Erdos240.BakerSourceAlgebraicIntegralGridGrowth.levelAlgebraicSourceRowError_integralTarget_le_threshold
