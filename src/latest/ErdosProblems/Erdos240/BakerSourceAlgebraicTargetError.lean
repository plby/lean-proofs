/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAlgebraicUniformBounds
import ErdosProblems.Erdos240.BakerSourceLiouvilleLowerBounds
import ErdosProblems.Erdos240.BakerSourceUniformConstantCompletion

/-!
# Absorbing the algebraic comparison error at integral targets

The complete uniform constant ledger makes the normalized small-form
exponent much larger than the four-height exponent in the integral
Liouville threshold.  This file isolates that scalar comparison, so the
Lemma-4 target-error callback follows immediately from the uniform
three-quarter row estimate.
-/

noncomputable section

namespace Erdos240.BakerSourceAlgebraicTargetError

open Erdos240
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerSourceLiouvilleLowerBounds
open BakerSourceUniformConstantCompletion

/-- The integral entry of the uniform ledger already implies the much
smaller structural inequality `16k ≤ C₀`. -/
theorem sixteen_mul_k_le_of_integralLedger {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) {C₀ : ℝ}
    (hintegral :
      16 * P.k * sourceIntegralDenominatorConstant P ≤ C₀) :
    16 * P.k ≤ C₀ := by
  have hk : (1 : ℝ) ≤ P.k := P.one_le_k
  have hOmega : (1 : ℝ) ≤ P.OmegaOld := P.one_le_OmegaOld
  have hfactor : (1 : ℝ) ≤ 8 * P.k * P.OmegaOld := by
    nlinarith [mul_pos P.k_pos P.OmegaOld_pos]
  have h16k0 : (0 : ℝ) ≤ 16 * P.k :=
    mul_nonneg (by norm_num) P.k_pos.le
  calc
    16 * P.k ≤ 16 * P.k * (8 * P.k * P.OmegaOld) := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hfactor h16k0)
    _ = 16 * P.k * sourceIntegralDenominatorConstant P := by
      unfold sourceIntegralDenominatorConstant
      ring
    _ ≤ C₀ := hintegral

/-- Three quarters of the normalized source exponent dominates four full
source-height units under the integral ledger entry. -/
theorem four_heightScale_le_three_quarters_sourceExponent
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {C₀ : ℝ}
    (hintegral :
      16 * P.k * sourceIntegralDenominatorConstant P ≤ C₀) :
    4 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) ≤
      3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4 := by
  have hC : 16 * P.k ≤ C₀ :=
    sixteen_mul_k_le_of_integralLedger P hintegral
  have hlogB : (P.h : ℝ) ≤ Real.log P.Bsrc := P.h_cast_le_log_Bsrc
  have hlogB0 : 0 ≤ Real.log P.Bsrc := P.two_le_log_Bsrc.trans' (by norm_num)
  have hk0 : 0 ≤ P.k := P.k_pos.le
  have hcoeff : 16 * (P.h : ℝ) * P.k ≤ C₀ * Real.log P.Bsrc := by
    calc
      16 * (P.h : ℝ) * P.k = (16 * P.k) * P.h := by ring
      _ ≤ (16 * P.k) * Real.log P.Bsrc :=
        mul_le_mul_of_nonneg_left hlogB (by positivity)
      _ ≤ C₀ * Real.log P.Bsrc :=
        mul_le_mul_of_nonneg_right hC hlogB0
  have hcommon :
      0 ≤ P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld :=
    mul_nonneg
      (mul_nonneg P.OmegaOld_pos.le P.log_newHeight_pos.le)
      P.log_OmegaOld_pos.le
  have hscaled := mul_le_mul_of_nonneg_right hcoeff hcommon
  have hstrong :
      16 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) ≤
        sourceExponent P (C₀ * Real.log P.OmegaOld) := by
    unfold sourceExponent VDPLParameters.Omega
    nlinarith
  have hheight0 :
      0 ≤ (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg P.h) P.k_pos.le)
        P.Omega_pos.le)
      P.log_OmegaOld_pos.le
  have hquarter :
      4 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) ≤
        sourceExponent P (C₀ * Real.log P.OmegaOld) / 4 := by
    linarith
  have hsource0 :
      0 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld) := by
    linarith
  calc
    4 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) ≤
        sourceExponent P (C₀ * Real.log P.OmegaOld) / 4 := hquarter
    _ ≤ 3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4 := by
      linarith

/-- The canonical three-quarter row-error envelope is strictly below the
integral Liouville threshold. -/
theorem exp_neg_three_quarters_sourceExponent_lt_integralThreshold
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (hJ : P.LevelOK J)
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Slevel J) {C₀ : ℝ}
    (hintegral :
      16 * P.k * sourceIntegralDenominatorConstant P ≤ C₀) :
    Real.exp (-3 * sourceExponent P
        (C₀ * Real.log P.OmegaOld) / 4) <
      stateIntegralLiouvilleThreshold P J m := by
  have hscale :=
    four_heightScale_le_three_quarters_sourceExponent P hintegral
  calc
    Real.exp (-3 * sourceExponent P
        (C₀ * Real.log P.OmegaOld) / 4) ≤
      Real.exp (-(4 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld))) := by
      exact Real.exp_le_exp.mpr (by linarith)
    _ < stateIntegralLiouvilleThreshold P J m :=
      exp_neg_four_heightScale_lt_stateIntegralLiouvilleThreshold P hJ m hm

end Erdos240.BakerSourceAlgebraicTargetError

#print axioms
  Erdos240.BakerSourceAlgebraicTargetError.four_heightScale_le_three_quarters_sourceExponent
#print axioms
  Erdos240.BakerSourceAlgebraicTargetError.exp_neg_three_quarters_sourceExponent_lt_integralThreshold
