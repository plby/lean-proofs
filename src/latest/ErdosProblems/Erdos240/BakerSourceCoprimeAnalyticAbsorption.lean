/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceInitialOuterBudget
import ErdosProblems.Erdos240.BakerSourcePositiveStageGrowth

/-!
# Fixed-height analytic absorption for source coprime completion

This module isolates the analytic calculation from the geometric bounds on
the p. 52 circle.  An algebraic bound `exp (4 H / 3)` and the usual
structural amplification bound imply an actual auxiliary-function bound
`exp (3 H / 2)`.
-/

noncomputable section

namespace Erdos240.BakerSourceCoprimeAnalyticAbsorption

open Erdos240
open BakerLemma2Concrete
open BakerLemma3
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerSourceAlgebraicUniformBounds
open BakerSourceLogFormNormalization
open BakerSourceMajorantClosedForm
open BakerSourceOversizedConstantNumerics
open BakerSourcePositiveStageGrowth
open BakerSourceState

/-- The structural amplification bound and the normalized small-form bound
leave a literal perturbation exponent of at most one. -/
theorem perturbationExponent_le_one
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (z : ℂ)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hamplification :
      (initialSupportBound P : ℝ) *
          (P.qInvPow (J + 1) * P.LlastZero) * ‖z‖ ≤
        Real.exp (sourceExponent P
          (P.C * Real.log P.OmegaOld) / 4)) :
    ((initialSupportBound P : ℝ) *
        (P.qInvPow (J + 1) * P.LlastZero) * ‖z‖) *
        smallLinearFormBound P (C₀ * Real.log P.OmegaOld) ≤ 1 := by
  let E : ℝ := sourceExponent P (C₀ * Real.log P.OmegaOld)
  let A : ℝ := (initialSupportBound P : ℝ) *
    (P.qInvPow (J + 1) * P.LlastZero) * ‖z‖
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    linarith
  have hA : A ≤ Real.exp (E / 16) := by
    exact hamplification.trans (by
      simpa only [E] using
        exp_quarter_le_exp_sixteenth_of_four_mul_le P hstruct)
  have hsmall :
      smallLinearFormBound P (C₀ * Real.log P.OmegaOld) =
        Real.exp (-E) := rfl
  change A * smallLinearFormBound P
      (C₀ * Real.log P.OmegaOld) ≤ 1
  rw [hsmall]
  calc
    A * Real.exp (-E) ≤ Real.exp (E / 16) * Real.exp (-E) :=
      mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
    _ = Real.exp (-15 * E / 16) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith)
    _ = 1 := Real.exp_zero

/-- Algebraic growth `exp (4H/3)` plus the normalized perturbation gives
the analytic closed form `exp (3H/2)`. -/
theorem analyticGrowth_le_exp_three_halves_of_coprimeBounds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (z : ℂ)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hgrowth :
      sourceSharpAlgebraicGrowthMajorant P (J + 1) z (P.Sstep J) ≤
        Real.exp ((4 / 3 : ℝ) * sourceHeightUnit P))
    (hamplification :
      (initialSupportBound P : ℝ) *
          (P.qInvPow (J + 1) * P.LlastZero) * ‖z‖ ≤
        Real.exp (sourceExponent P
          (P.C * Real.log P.OmegaOld) / 4)) :
    sourceSharpAnalyticGrowthMajorant P (J + 1) z (P.Sstep J)
        (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) ≤
      Real.exp ((3 / 2 : ℝ) * sourceHeightUnit P) := by
  have hperturb := perturbationExponent_le_one
    P z hstruct hE hamplification
  unfold sourceSharpAnalyticGrowthMajorant
  calc
    sourceSharpAlgebraicGrowthMajorant P (J + 1) z (P.Sstep J) *
          Real.exp (((initialSupportBound P : ℝ) *
            (P.qInvPow (J + 1) * P.LlastZero) * ‖z‖) *
              smallLinearFormBound P
                (C₀ * Real.log P.OmegaOld)) ≤
        Real.exp ((4 / 3 : ℝ) * sourceHeightUnit P) * Real.exp 1 := by
      exact mul_le_mul hgrowth (Real.exp_le_exp.mpr hperturb)
        (Real.exp_pos _).le
        (Real.exp_pos _).le
    _ = Real.exp ((4 / 3 : ℝ) * sourceHeightUnit P + 1) := by
      rw [← Real.exp_add]
    _ ≤ Real.exp ((3 / 2 : ℝ) * sourceHeightUnit P) := by
      apply Real.exp_le_exp.mpr
      have hH : (26 / 3 : ℝ) < sourceHeightUnit P := by
        simpa only [sourceHeightUnit] using
          P.twentySix_thirds_lt_sourceHeightUnit
      nlinarith

/-- Direct actual-function consumer of the fixed-height analytic
absorption. -/
theorem norm_f_le_exp_three_halves_of_coprimeBounds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P (J + 1)) (b : Fin oldRank → ℤ)
    {bLast : ℤ} (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (z : ℂ) (m : VDPLMultiIndex P.rank)
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep J)
    (hgrowth :
      sourceSharpAlgebraicGrowthMajorant P (J + 1) z (P.Sstep J) ≤
        Real.exp ((4 / 3 : ℝ) * sourceHeightUnit P))
    (hamplification :
      (initialSupportBound P : ℝ) *
          (P.qInvPow (J + 1) * P.LlastZero) * ‖z‖ ≤
        Real.exp (sourceExponent P
          (P.C * Real.log P.OmegaOld) / 4)) :
    ‖f state b bLast z m‖ ≤
      Real.exp ((3 / 2 : ℝ) * sourceHeightUnit P) := by
  have hform := norm_logForm_le_smallLinearFormBound_of_normalized
    P C₀ b bLast hsmall
  refine (norm_f_le_sharpClosedForm P state b hb hbLastBound hbLast z m
    hm (by unfold smallLinearFormBound; positivity) hform).trans ?_
  exact analyticGrowth_le_exp_three_halves_of_coprimeBounds
    P J z hstruct hE hgrowth hamplification

end Erdos240.BakerSourceCoprimeAnalyticAbsorption

#print axioms
  Erdos240.BakerSourceCoprimeAnalyticAbsorption.perturbationExponent_le_one
#print axioms
  Erdos240.BakerSourceCoprimeAnalyticAbsorption.analyticGrowth_le_exp_three_halves_of_coprimeBounds
#print axioms
  Erdos240.BakerSourceCoprimeAnalyticAbsorption.norm_f_le_exp_three_halves_of_coprimeBounds
