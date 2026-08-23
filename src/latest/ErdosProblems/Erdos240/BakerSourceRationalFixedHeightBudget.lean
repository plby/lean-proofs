/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceRationalSharpBudget
import ErdosProblems.Erdos240.BakerLemma3Concrete
import ErdosProblems.Erdos240.BakerSourceUniformConstantCompletion
import ErdosProblems.Erdos240.BakerSourceRationalExactLiouville

/-!
# Fixed-height strictness for source Lemma 5

The rational Liouville threshold naturally has exponent
`(5 + 34 * 13^(oldRank+1)) * H`, where
`H = h * k * Omega * log OmegaOld`.  The sharp terminal contour has one
additional height unit.  This file records the two elementary estimates
needed to retain that unit:

* a fixed-family lower bound on the freely enlarged normalized constant
  makes the local Hermite term no larger than the strong scale; and
* two terms at the strong scale have sum strictly below the weak scale.

The second point is essential.  Merely proving the outer remainder smaller
than a non-strict Liouville lower bound at the same exponent cannot absorb
the positive local Hermite term.
-/

noncomputable section

namespace Erdos240.VDPLParameters

open Erdos240.BakerLemma3Concrete
open Erdos240.BakerSourceUniformConstantCompletion

variable {oldRank : ℕ} [Nonempty (Fin oldRank)]
  (P : VDPLParameters (Fin oldRank))

/-- The existing fixed-family ledger already dominates the extra exact-degree
requirement used below; no new uniform constant has to be chosen. -/
theorem exactRationalFixedHeight_requirement_of_fixedBounds
    {C₀ : ℝ} (hfixed : HasFixedSourceConstantBounds P C₀) :
    2 * (6 + 34 * (13 ^ (oldRank + 1) : ℝ)) * P.k ≤ C₀ := by
  let d : ℝ := (13 ^ (oldRank + 1) : ℝ)
  let u : ℝ := P.k ^ (1 / 2 : ℝ)
  let v : ℝ := P.k ^ (1 / 6 : ℝ)
  have hdv : d ≤ v := by
    simpa only [d, v] using P.sourceRadicalDegree_le_k_rpow_one_sixth
  have hvu : v ≤ u := by
    have h128 := P.oneTwentyEight_mul_k_rpow_one_sixth_le_k_rpow_half
    have hv0 : 0 ≤ v := by
      dsimp only [v]
      exact Real.rpow_nonneg (P.k_pos.le) (1 / 6 : ℝ)
    dsimp only [u, v] at h128 ⊢
    nlinarith
  have hk0 : 0 ≤ P.k := P.k_pos.le
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have hcoeff :
      2 * (6 + 34 * d) ≤
        4 * (5 + u * (P.k + 32)) := by
    nlinarith
  have hmul :
      2 * (6 + 34 * d) * P.k ≤
        4 * (5 + u * (P.k + 32)) * P.k :=
    mul_le_mul_of_nonneg_right hcoeff hk0
  have hledger :
      4 * sourceRationalLiouvilleConstant P * P.k ≤ C₀ :=
    hfixed.2.2.2.2.1
  have hconstant :
      sourceRationalLiouvilleConstant P = 5 + u * (P.k + 32) := by
    unfold sourceRationalLiouvilleConstant
    dsimp only [u]
    rw [P.mu_eq]
  simpa only [hconstant] using hmul.trans hledger

/-- A convenient fixed-family requirement which puts the local
`exp (-7E/12)` term below the rational strong scale
`(6 + 34d) * H`, with `d = 13^(oldRank+1)`. -/
theorem exactRationalStrongScale_le_seven_twelfths_sourceExponent
    {C₀ : ℝ}
    (hC₀ : 2 * (6 + 34 * (13 ^ (oldRank + 1) : ℝ)) * P.k ≤ C₀) :
    (6 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) ≤
      7 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 12 := by
  let a : ℝ := 6 + 34 * (13 ^ (oldRank + 1) : ℝ)
  let W : ℝ := P.Omega * Real.log P.OmegaOld
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have hC₀pos : 0 < C₀ := by
    have hk : 0 < 2 * a * P.k := mul_pos (mul_pos (by norm_num) ha) P.k_pos
    exact hk.trans_le (by simpa only [a] using hC₀)
  have hcoeff : a * P.k ≤ (7 / 12 : ℝ) * C₀ := by
    have hhalf : a * P.k ≤ C₀ / 2 := by
      nlinarith [show 2 * a * P.k ≤ C₀ by simpa only [a] using hC₀]
    nlinarith
  have hW : 0 < W := by
    dsimp only [W]
    exact mul_pos P.Omega_pos P.log_OmegaOld_pos
  have hhW : 0 ≤ (P.h : ℝ) * W := by positivity
  have hlogW :
      (P.h : ℝ) * W ≤ Real.log (P.Bsrc : ℝ) * W :=
    mul_le_mul_of_nonneg_right P.h_cast_le_log_Bsrc hW.le
  calc
    (6 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) =
      (a * P.k) * ((P.h : ℝ) * W) := by
        simp only [a, W]
        ring
    _ ≤ ((7 / 12 : ℝ) * C₀) * ((P.h : ℝ) * W) :=
      mul_le_mul_of_nonneg_right hcoeff hhW
    _ ≤ ((7 / 12 : ℝ) * C₀) *
        (Real.log (P.Bsrc : ℝ) * W) :=
      mul_le_mul_of_nonneg_left hlogW (by positivity)
    _ = 7 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 12 := by
      dsimp only [W]
      unfold sourceExponent VDPLParameters.Omega
      ring

/-- Exponential form of
`exactRationalStrongScale_le_seven_twelfths_sourceExponent`. -/
theorem exp_neg_seven_twelfths_sourceExponent_le_exactRationalStrongScale
    {C₀ : ℝ}
    (hC₀ : 2 * (6 + 34 * (13 ^ (oldRank + 1) : ℝ)) * P.k ≤ C₀) :
    Real.exp (-7 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 12) ≤
      Real.exp (-((6 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
  apply Real.exp_le_exp.mpr
  have h := P.exactRationalStrongScale_le_seven_twelfths_sourceExponent hC₀
  linarith

/-- The one-height-unit gap from the strong rational scale to the weak
Liouville scale absorbs the sum of the local and outer terms. -/
theorem two_exp_neg_exactRationalStrongScale_lt_exactRationalWeakScale :
    Real.exp (-((6 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) +
      Real.exp (-((6 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) <
    Real.exp (-((5 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
      ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
  let d : ℝ := (13 ^ (oldRank + 1) : ℝ)
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  have hH : 1 ≤ H := by
    dsimp only [H]
    exact P.one_le_sourceHeightUnit
  have hlog : Real.log 2 < H := by
    have : Real.log 2 < (1 : ℝ) := by
      nlinarith [Real.log_two_lt_d9]
    exact this.trans_le hH
  calc
    Real.exp (-((6 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
          ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) +
        Real.exp (-((6 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
          ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) =
      Real.exp (Real.log 2 - (6 + 34 * d) * H) := by
        rw [sub_eq_add_neg, Real.exp_add,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        dsimp only [d, H]
        ring
    _ < Real.exp (-(5 + 34 * d) * H) := by
      apply Real.exp_lt_exp.mpr
      linarith
    _ = Real.exp (-((5 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
      dsimp only [d, H]
      congr 1
      ring

/-- Ready scalar comparison for the two source Lemma-5 terms. -/
theorem exp_neg_seven_twelfths_add_exactStrong_lt_exactWeak
    {C₀ : ℝ}
    (hC₀ : 2 * (6 + 34 * (13 ^ (oldRank + 1) : ℝ)) * P.k ≤ C₀) :
    Real.exp (-7 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 12) +
        Real.exp (-((6 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
          ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) <
      Real.exp (-((5 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
        ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
  exact (add_le_add
      (P.exp_neg_seven_twelfths_sourceExponent_le_exactRationalStrongScale hC₀)
      le_rfl).trans_lt P.two_exp_neg_exactRationalStrongScale_lt_exactRationalWeakScale

/-- Direct threshold comparison needed by the predicate-level source Lemma 5.
The only pointwise hypothesis is the level-scaled algebraic growth estimate
also used by the exact-degree Liouville bound. -/
theorem hermite_add_outer_lt_stateRationalLiouvilleThreshold
    {J : ℕ} (hJ : P.LevelOK J)
    (state : BakerSourceState.LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    {C₀ : ℝ} (hfixed : HasFixedSourceConstantBounds P C₀)
    (l : ℕ) (hl : l ≤ P.R (J + 1))
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep J)
    (hgrowth :
      (BakerSourceAlgebraicLevelMajorant.levelAlgebraicExponentialMajorant
        P state b bLast ((l : ℂ) / (P.q : ℂ)) m).growth ≤
          Real.exp (2 * BakerSourceRationalLiouvilleLowerBounds.rationalHeightScale P)) :
    Real.exp (-7 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 12) +
        Real.exp (-((6 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
          ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) <
      BakerLemma3Instantiation.stateRationalLiouvilleThreshold
        P J state b bLast l m := by
  have hC₀ := P.exactRationalFixedHeight_requirement_of_fixedBounds hfixed
  have hsum :=
    P.exp_neg_seven_twelfths_add_exactStrong_lt_exactWeak hC₀
  have hlower :=
    BakerSourceRationalLiouvilleLowerBounds.exp_neg_exactDegreeScale_le_stateRationalLiouvilleThreshold
      P hJ state b bLast l hl m hm hgrowth
  exact hsum.trans_le hlower

end Erdos240.VDPLParameters

#print axioms
  Erdos240.VDPLParameters.exactRationalFixedHeight_requirement_of_fixedBounds
#print axioms
  Erdos240.VDPLParameters.exactRationalStrongScale_le_seven_twelfths_sourceExponent
#print axioms
  Erdos240.VDPLParameters.exp_neg_seven_twelfths_sourceExponent_le_exactRationalStrongScale
#print axioms
  Erdos240.VDPLParameters.two_exp_neg_exactRationalStrongScale_lt_exactRationalWeakScale
#print axioms
  Erdos240.VDPLParameters.exp_neg_seven_twelfths_add_exactStrong_lt_exactWeak
#print axioms
  Erdos240.VDPLParameters.hermite_add_outer_lt_stateRationalLiouvilleThreshold
