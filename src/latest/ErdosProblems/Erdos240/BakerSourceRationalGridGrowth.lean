/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAlgebraicStaticFactors
import ErdosProblems.Erdos240.BakerSourcePositiveStageGrowth

/-!
# Source-faithful growth on the rational grid

This file closes the numerical growth estimate used in source Lemma 5.
At a rational target `l / q`, with `l ≤ R (J+1)`, the factor `q⁻ᴶ` in
the algebraic exponential cancels the grid radius.  The large fixed seed
for `k^sigma` then absorbs all remaining Delta and exponential factors in
the fixed height unit `H = h*k*Omega*log OmegaOld`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceRationalGridGrowth

open Finset
open Erdos240
open BakerLemma2Concrete
open BakerLemma3
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerSourceAlgebraicLevelMajorant
open BakerSourceAlgebraicMajorant
open BakerSourceAlgebraicStaticFactors
open BakerSourceAlgebraicUniformBounds
open BakerSourceMajorantClosedForm
open BakerSourcePositiveStageGrowth
open BakerSourceState

/-- The rational target has scaled norm at most the source radius `16h`. -/
theorem norm_scaledArgument_ratCast_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J l : ℕ}
    (hl : l ≤ P.R (J + 1)) :
    ‖scaledArgument P.q J ((l : ℂ) / (P.q : ℂ))‖ ≤ 16 * P.h := by
  unfold scaledArgument
  rw [norm_div, norm_div, norm_pow, Complex.norm_natCast,
    Complex.norm_natCast]
  have hq : (0 : ℝ) < P.q := by
    exact_mod_cast Nat.zero_lt_of_lt P.one_lt_q
  have hqpow : (0 : ℝ) < (P.q : ℝ) ^ J := pow_pos hq J
  have hlR : (l : ℝ) ≤ P.R (J + 1) := by exact_mod_cast hl
  rw [div_div]
  rw [div_le_iff₀ (mul_pos hq hqpow)]
  calc
    (l : ℝ) ≤ P.R (J + 1) := hlR
    _ = (16 * P.h : ℝ) * ((P.q : ℝ) * (P.q : ℝ) ^ J) := by
      unfold VDPLParameters.R
      rw [pow_succ]
      push_cast
      ring

/-- The rational-grid derivative budget consumes at most one quarter of
the fixed height unit in the `(2B)^S` factor. -/
theorem rational_oldDeltaPower_le_exp_quarter {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) (J : ℕ) :
    (((2 * P.Bsrc : ℕ) : ℝ) ^ P.Sstep J) ≤
      Real.exp ((1 / 4 : ℝ) * sourceHeightUnit P) := by
  have hBpos : 0 < P.Bsrc := by
    have : (0 : ℝ) < P.Bsrc :=
      (Real.exp_pos 2).trans_le P.Bsrc_lower
    exact_mod_cast this
  apply VDPLParameters.pow_le_exp_of_mul_log_le (by positivity)
  have hbudget : (P.Sstep J : ℝ) ≤ P.levelScale J / 9 := by
    unfold VDPLParameters.Sstep
    exact Nat.floor_le
      (div_nonneg (P.levelScale_pos J).le (by norm_num))
  have hlog := log_two_mul_Bsrc_le_two_h P
  have hlognonneg : 0 ≤ Real.log (((2 * P.Bsrc : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    have hB : 1 ≤ P.Bsrc := by
      have hBreal : (1 : ℝ) ≤ P.Bsrc :=
        (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans P.Bsrc_lower
      exact_mod_cast hBreal
    exact_mod_cast (show 1 ≤ 2 * P.Bsrc by omega)
  have hlog' : Real.log (((2 * P.Bsrc : ℕ) : ℝ)) ≤ 2 * P.h := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlog
  have hfirst :
      (P.Sstep J : ℝ) * Real.log (((2 * P.Bsrc : ℕ) : ℝ)) ≤
        (2 / 9 : ℝ) * P.h * P.levelScale J := by
    calc
      (P.Sstep J : ℝ) * Real.log (((2 * P.Bsrc : ℕ) : ℝ)) ≤
          (P.levelScale J / 9) * (2 * P.h) :=
        mul_le_mul hbudget hlog' hlognonneg
          (div_nonneg (P.levelScale_pos J).le (by norm_num))
      _ = (2 / 9 : ℝ) * P.h * P.levelScale J := by ring
  have hq : P.qInvPow J ≤ 1 := by
    have h := P.qInvPow_antitone (Nat.zero_le J)
    simpa [VDPLParameters.qInvPow] using h
  have hcore : 0 ≤ P.k * P.Omega * Real.log P.OmegaOld :=
    mul_nonneg (mul_nonneg P.k_pos.le P.Omega_pos.le)
      P.log_OmegaOld_pos.le
  have hscale : P.levelScale J ≤
      P.k * P.Omega * Real.log P.OmegaOld := by
    unfold VDPLParameters.levelScale
    calc
      P.qInvPow J * P.k * P.Omega * Real.log P.OmegaOld =
          P.qInvPow J *
            (P.k * P.Omega * Real.log P.OmegaOld) := by ring
      _ ≤ 1 * (P.k * P.Omega * Real.log P.OmegaOld) :=
        mul_le_mul_of_nonneg_right hq hcore
      _ = P.k * P.Omega * Real.log P.OmegaOld := by ring
  calc
    (P.Sstep J : ℝ) * Real.log (((2 * P.Bsrc : ℕ) : ℝ)) ≤
        (2 / 9 : ℝ) * P.h * P.levelScale J := hfirst
    _ ≤ (2 / 9 : ℝ) * P.h *
        (P.k * P.Omega * Real.log P.OmegaOld) := by
      gcongr
    _ ≤ (1 / 4 : ℝ) * sourceHeightUnit P := by
      unfold sourceHeightUnit
      have hnonneg : 0 ≤
          (P.h : ℝ) * (P.k * P.Omega * Real.log P.OmegaOld) := by positivity
      nlinarith

/-- The level-scaled binary side factor is bounded by its initial value,
and hence costs at most `H/32`. -/
theorem rational_oldDeltaSidePower_le_exp_thirtySecond {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) (J : ℕ) :
    (2 : ℝ) ^ levelOldDeltaSideSum P J ≤
      Real.exp ((1 / 32 : ℝ) * sourceHeightUnit P) := by
  have hside : levelOldDeltaSideSum P J ≤
      ∑ r : Fin oldRank, (P.LiZero r + P.LlastZero) := by
    unfold levelOldDeltaSideSum
    apply Finset.sum_le_sum
    intro r _hr
    exact Nat.add_le_add
      (levelBoxShape_oldMax_le_initial P J r)
      (levelBoxShape_lastMax_le_initial P J)
  have hpow : (2 : ℝ) ^ levelOldDeltaSideSum P J ≤
      (2 : ℝ) ^ (∑ r : Fin oldRank, (P.LiZero r + P.LlastZero)) :=
    pow_le_pow_right₀ (by norm_num) hside
  exact hpow.trans (by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, sourceHeightUnit] using
      initial_oldDeltaSideFactor_le P)

/-- The powered head Delta on the rational grid costs at most `H/32`. -/
theorem rational_sourceHeadDeltaMajorant_le_exp_thirtySecond
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J l : ℕ}
    (hl : l ≤ P.R (J + 1)) :
    sourceHeadDeltaMajorant P J ((l : ℂ) / (P.q : ℂ)) ≤
      Real.exp ((1 / 32 : ℝ) * sourceHeightUnit P) := by
  have hscaled := norm_scaledArgument_ratCast_le P hl
  refine (sourceHeadDeltaMajorant_le_of_scaledNorm_le
    P J ((l : ℂ) / (P.q : ℂ)) hscaled).trans ?_
  have hh : 1 ≤ P.h := P.one_le_h
  have hx : (16 : ℝ) * (P.h : ℝ) + P.h =
      ((17 * P.h : ℕ) : ℝ) := by
    push_cast
    ring
  have hceil : Nat.ceil ((16 : ℝ) * (P.h : ℝ) + P.h) = 17 * P.h := by
    rw [hx, Nat.ceil_natCast]
  have hpow :
      (2 : ℝ) ^
          ((Nat.ceil ((16 : ℝ) * P.h + P.h) + 1 + P.h) *
            P.LzeroPlusOne) ≤
        (4 : ℝ) ^ ((P.Lzero + 1) * (18 * P.h)) := by
    rw [P.Lzero_add_one_eq_LzeroPlusOne]
    rw [hceil]
    have hcount : 17 * P.h + 1 + P.h ≤ 2 * (18 * P.h) := by omega
    have hexp :
        (17 * P.h + 1 + P.h) * P.LzeroPlusOne ≤
          2 * (P.LzeroPlusOne * (18 * P.h)) := by
      calc
        (17 * P.h + 1 + P.h) * P.LzeroPlusOne ≤
            (2 * (18 * P.h)) * P.LzeroPlusOne :=
          Nat.mul_le_mul_right P.LzeroPlusOne hcount
        _ = 2 * (P.LzeroPlusOne * (18 * P.h)) := by ring
    calc
      (2 : ℝ) ^
          ((17 * P.h + 1 + P.h) * P.LzeroPlusOne) ≤
        (2 : ℝ) ^ (2 * (P.LzeroPlusOne * (18 * P.h))) :=
          pow_le_pow_right₀ (by norm_num) hexp
      _ = (4 : ℝ) ^ (P.LzeroPlusOne * (18 * P.h)) := by
        rw [pow_mul]
        norm_num
  exact hpow.trans (by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, sourceHeightUnit] using
      initial_headSideFactor_le P)

/-- The level-scaled algebraic exponential on a rational target costs at
most `H/32`; this is the fixed-seed `k^sigma ≥ 256` reserve. -/
theorem rational_algebraicRateMajorant_le_exp_thirtySecond
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J l : ℕ}
    (hl : l ≤ P.R (J + 1)) :
    Real.exp (P.qInvPow J * sourceAlgebraicRateBound P *
        ‖((l : ℂ) / (P.q : ℂ))‖) ≤
      Real.exp ((1 / 32 : ℝ) * sourceHeightUnit P) := by
  apply Real.exp_le_exp.mpr
  have hrate := sourceAlgebraicRateBound_le_eighth P
  have hscaled := norm_scaledArgument_ratCast_le P hl
  have hscaleEq : P.qInvPow J * ‖((l : ℂ) / (P.q : ℂ))‖ =
      ‖scaledArgument P.q J ((l : ℂ) / (P.q : ℂ))‖ := by
    unfold scaledArgument VDPLParameters.qInvPow
    simp only [norm_div, Complex.norm_natCast, Nat.cast_pow]
    field_simp
    rw [norm_pow, Complex.norm_natCast]
    ring
  have hfirst :
      P.qInvPow J * sourceAlgebraicRateBound P *
          ‖((l : ℂ) / (P.q : ℂ))‖ ≤
        2 * P.h * P.k ^ (1 - P.sigma) * P.Omega *
          Real.log P.OmegaOld := by
    calc
      P.qInvPow J * sourceAlgebraicRateBound P *
          ‖((l : ℂ) / (P.q : ℂ))‖ =
        sourceAlgebraicRateBound P *
          (P.qInvPow J * ‖((l : ℂ) / (P.q : ℂ))‖) := by ring
      _ = sourceAlgebraicRateBound P *
          ‖scaledArgument P.q J ((l : ℂ) / (P.q : ℂ))‖ := by rw [hscaleEq]
      _ ≤ ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
          Real.log P.OmegaOld) * (16 * P.h) :=
        mul_le_mul hrate hscaled (norm_nonneg _)
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) (Real.rpow_nonneg P.k_pos.le _))
              P.Omega_pos.le) P.log_OmegaOld_pos.le)
      _ = 2 * P.h * P.k ^ (1 - P.sigma) * P.Omega *
          Real.log P.OmegaOld := by ring
  have hks := twoHundredFiftySix_le_k_rpow_sigma P
  have hreserve : (64 : ℝ) ≤ P.k ^ P.sigma := by linarith
  calc
    P.qInvPow J * sourceAlgebraicRateBound P *
        ‖((l : ℂ) / (P.q : ℂ))‖ ≤
      2 * P.h * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld := hfirst
    _ = (1 / 32 : ℝ) * P.h * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld * 64 := by ring
    _ ≤ (1 / 32 : ℝ) * P.h * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld * P.k ^ P.sigma := by
      exact mul_le_mul_of_nonneg_left hreserve
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) (by positivity))
              (Real.rpow_nonneg P.k_pos.le _)) P.Omega_pos.le)
          P.log_OmegaOld_pos.le)
    _ = (1 / 32 : ℝ) * P.h *
        (P.k ^ (1 - P.sigma) * P.k ^ P.sigma) * P.Omega *
          Real.log P.OmegaOld := by ring
    _ = (1 / 32 : ℝ) * sourceHeightUnit P := by
      rw [k_rpow_one_sub_sigma_mul_rpow_sigma P]
      unfold sourceHeightUnit
      ring

/-- Closed sharp algebraic growth at every rational Lemma-5 target. -/
theorem sourceSharpAlgebraicGrowthMajorant_ratCast_le_exp_two
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    {J l : ℕ} (hl : l ≤ P.R (J + 1)) :
    sourceSharpAlgebraicGrowthMajorant P J
        ((l : ℂ) / (P.q : ℂ)) (P.Sstep J) ≤
      Real.exp (2 * sourceHeightUnit P) := by
  let H : ℝ := sourceHeightUnit P
  have hstatic := support_sq_mul_coeffHeight_le_exp_two_thirds P hreq
  have hold := rational_oldDeltaPower_le_exp_quarter P J
  have hside := rational_oldDeltaSidePower_le_exp_thirtySecond P J
  have hhead := rational_sourceHeadDeltaMajorant_le_exp_thirtySecond P hl
  have hrate := rational_algebraicRateMajorant_le_exp_thirtySecond P hl
  have hstatic' :
      (initialSupportBound P : ℝ) *
          (P.coeffHeight * (initialSupportBound P : ℝ)) ≤
        Real.exp ((2 / 3 : ℝ) * H) := by
    simpa only [H, sourceHeightUnit] using hstatic
  have hold' : (((2 * P.Bsrc : ℕ) : ℝ) ^ P.Sstep J) ≤
      Real.exp (H / 4) := by
    convert hold using 1 <;> dsimp only [H] <;> ring
  have hside' : (2 : ℝ) ^ levelOldDeltaSideSum P J ≤
      Real.exp (H / 32) := by
    convert hside using 1 <;> dsimp only [H] <;> ring
  have hhead' :
      sourceHeadDeltaMajorant P J ((l : ℂ) / (P.q : ℂ)) ≤
        Real.exp (H / 32) := by
    convert hhead using 1 <;> dsimp only [H] <;> ring
  have hrate' :
      Real.exp (P.qInvPow J * sourceAlgebraicRateBound P *
        ‖((l : ℂ) / (P.q : ℂ))‖) ≤ Real.exp (H / 32) := by
    convert hrate using 1 <;> dsimp only [H] <;> ring
  have hprod1 :
      ((initialSupportBound P : ℝ) *
          (P.coeffHeight * (initialSupportBound P : ℝ))) *
          (((2 * P.Bsrc : ℕ) : ℝ) ^ P.Sstep J) ≤
        Real.exp ((2 / 3 : ℝ) * H) * Real.exp (H / 4) :=
    mul_le_mul hstatic' hold' (by positivity) (by positivity)
  have hprod2 :
      (((initialSupportBound P : ℝ) *
          (P.coeffHeight * (initialSupportBound P : ℝ))) *
          (((2 * P.Bsrc : ℕ) : ℝ) ^ P.Sstep J)) *
          sourceHeadDeltaMajorant P J ((l : ℂ) / (P.q : ℂ)) ≤
        (Real.exp ((2 / 3 : ℝ) * H) * Real.exp (H / 4)) *
          Real.exp (H / 32) :=
    mul_le_mul hprod1 hhead'
      (by unfold sourceHeadDeltaMajorant; positivity) (by positivity)
  have hprod3 :
      ((((initialSupportBound P : ℝ) *
          (P.coeffHeight * (initialSupportBound P : ℝ))) *
          (((2 * P.Bsrc : ℕ) : ℝ) ^ P.Sstep J)) *
          sourceHeadDeltaMajorant P J ((l : ℂ) / (P.q : ℂ))) *
          (2 : ℝ) ^ levelOldDeltaSideSum P J ≤
        ((Real.exp ((2 / 3 : ℝ) * H) * Real.exp (H / 4)) *
          Real.exp (H / 32)) * Real.exp (H / 32) :=
    mul_le_mul hprod2 hside' (by positivity) (by positivity)
  have hprod4 :
      (((((initialSupportBound P : ℝ) *
          (P.coeffHeight * (initialSupportBound P : ℝ))) *
          (((2 * P.Bsrc : ℕ) : ℝ) ^ P.Sstep J)) *
          sourceHeadDeltaMajorant P J ((l : ℂ) / (P.q : ℂ))) *
          (2 : ℝ) ^ levelOldDeltaSideSum P J) *
          Real.exp (P.qInvPow J * sourceAlgebraicRateBound P *
            ‖((l : ℂ) / (P.q : ℂ))‖) ≤
        (((Real.exp ((2 / 3 : ℝ) * H) * Real.exp (H / 4)) *
          Real.exp (H / 32)) * Real.exp (H / 32)) *
            Real.exp (H / 32) :=
    mul_le_mul hprod3 hrate' (by positivity) (by positivity)
  have hraw :
      sourceSharpAlgebraicGrowthMajorant P J
          ((l : ℂ) / (P.q : ℂ)) (P.Sstep J) ≤
        Real.exp ((2 / 3 : ℝ) * H) * Real.exp (H / 4) *
          Real.exp (H / 32) * Real.exp (H / 32) * Real.exp (H / 32) := by
    unfold sourceSharpAlgebraicGrowthMajorant
      sourceSharpDeltaFactorMajorant
    convert hprod4 using 1 <;> ring
  calc
    sourceSharpAlgebraicGrowthMajorant P J
        ((l : ℂ) / (P.q : ℂ)) (P.Sstep J) ≤
      Real.exp ((2 / 3 : ℝ) * H) * Real.exp (H / 4) *
        Real.exp (H / 32) * Real.exp (H / 32) * Real.exp (H / 32) := hraw
    _ = Real.exp (((2 / 3 : ℝ) * H) + H / 4 + H / 32 + H / 32 + H / 32) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (2 * H) := by
      apply Real.exp_le_exp.mpr
      have hH : 0 ≤ H := (sourceHeightUnit_pos P).le
      linarith
    _ = Real.exp (2 * sourceHeightUnit P) := rfl

/-- Premise-free source Lemma-5 grid growth for the actual level-scaled
algebraic majorant. -/
theorem levelAlgebraicGrowth_ratCast_le_exp_two
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLast : bLast.natAbs ≤ P.Bsrc)
    {l : ℕ} (hl : l ≤ P.R (J + 1))
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep J) :
    (levelAlgebraicExponentialMajorant P state b bLast
      ((l : ℂ) / (P.q : ℂ)) m).growth ≤
      Real.exp (2 * sourceHeightUnit P) := by
  exact (levelAlgebraicGrowth_le_sharpClosedForm
    P state b bLast hb hbLast ((l : ℂ) / (P.q : ℂ)) m hm).trans
      (sourceSharpAlgebraicGrowthMajorant_ratCast_le_exp_two P hreq hl)

#print axioms norm_scaledArgument_ratCast_le
#print axioms rational_oldDeltaPower_le_exp_quarter
#print axioms rational_oldDeltaSidePower_le_exp_thirtySecond
#print axioms rational_sourceHeadDeltaMajorant_le_exp_thirtySecond
#print axioms rational_algebraicRateMajorant_le_exp_thirtySecond
#print axioms sourceSharpAlgebraicGrowthMajorant_ratCast_le_exp_two
#print axioms levelAlgebraicGrowth_ratCast_le_exp_two

end Erdos240.BakerSourceRationalGridGrowth
