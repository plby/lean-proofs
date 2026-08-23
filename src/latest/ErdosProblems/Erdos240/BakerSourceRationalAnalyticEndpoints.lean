/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerLemma5Concrete
import ErdosProblems.Erdos240.BakerSourceAlgebraicIntegralGridGrowth
import ErdosProblems.Erdos240.BakerSourceRationalAlternativeIndependent
import ErdosProblems.Erdos240.BakerSourceRationalFixedHeightBudget
import ErdosProblems.Erdos240.BakerSourceRationalGridGrowth

/-!
# Closed analytic endpoints on the source Lemma-5 rational grid

This file discharges the analytic premises left by the exact source
Lemma-5 interpolation theorem.  The terminal integral grid is the terminal
Lemma-4 disk, so its pointwise comparison error follows from the full-disk
algebraic estimate.  The same disk contains every rational target `l / q`.
Finally, the checked positive-contour estimate supplies the honest analytic
outer growth `exp (2 H + 24 H_t)`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceRationalAnalyticEndpoints

open Complex Metric
open Erdos240
open BakerInduction
open BakerLemma2Concrete
open BakerLemma3
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerLemma4InnerInduction
open BakerLemma5Concrete
open BakerSourceAlgebraicIntegralGridGrowth
open BakerSourceAlgebraicLevelMajorant
open BakerSourceAlgebraicMomentBounds
open BakerSourceAlgebraicUniformBounds
open BakerSourceLogFormNormalization
open BakerSourcePositiveStageGrowth
open BakerSourceRationalAlternativeIndependent
open BakerSourceRationalGridGrowth
open BakerSourceRationalLiouvilleLowerBounds
open BakerSourceState
open BakerSourceUniformConstantCompletion

/-- The last positive Lemma-4 stage. -/
private def terminalPositiveStage {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℕ :=
  3 * (P.rank + 1) - 1

private theorem terminalPositiveStage_lt {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    terminalPositiveStage P < terminalStage P := by
  unfold terminalPositiveStage terminalStage
  omega

private theorem terminalPositiveStage_succ {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    terminalPositiveStage P + 1 = terminalStage P := by
  unfold terminalPositiveStage terminalStage
  omega

/-- Every Lemma-5 rational target lies in the terminal Lemma-4 disk. -/
theorem norm_ratCast_div_le_terminalDisk {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank))
    {N l : ℕ} (hl : l ≤ P.R (N + 1)) :
    ‖(l : ℂ) / (P.q : ℂ)‖ ≤
      3 * P.lemmaFourRadius N
        (terminalPositiveStage P + 1) := by
  have hq : (1 : ℝ) ≤ P.q := by
    exact_mod_cast (Nat.succ_le_iff.mpr
      (Nat.zero_lt_of_lt P.one_lt_q))
  have hlNode : l ≤ sourceRationalNodeRadius P N :=
    hl.trans (targetRadius_le_sourceRationalNodeRadius P N)
  rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
  have hdiv : (l : ℝ) / P.q ≤ l := by
    exact div_le_self (Nat.cast_nonneg l) hq
  have hnode : (l : ℝ) ≤ sourceRationalNodeRadius P N := by
    exact_mod_cast hlNode
  have hradius : sourceRationalNodeRadius P N =
      P.lemmaFourRadius N (terminalPositiveStage P + 1) := by
    simp only [sourceRationalNodeRadius, terminalPositiveStage_succ,
      terminalStage]
  rw [hradius] at hnode
  have hnonneg : (0 : ℝ) ≤
      P.lemmaFourRadius N (terminalPositiveStage P + 1) := by positivity
  nlinarith

/-- The level-scaled algebraic row error at a rational Lemma-5 target has
the canonical three-quarter source-exponent bound. -/
theorem levelAlgebraicSourceRowError_ratCast_le_three_quarters
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    {N : ℕ} (state : LevelState P N) (b : Fin oldRank → ℤ)
    {bLast : ℤ} (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    {l : ℕ} (hl : l ≤ P.R (N + 1))
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep N)
    {C₀ : ℝ} (hfixed : HasFixedSourceConstantBounds P C₀) :
    levelAlgebraicSourceRowError P state b bLast
        ((l : ℂ) / (P.q : ℂ))
        (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) m ≤
      Real.exp (-3 * sourceExponent P
        (C₀ * Real.log P.OmegaOld) / 4) := by
  have ht := terminalPositiveStage_lt P
  have hz := norm_ratCast_div_le_terminalDisk P hl
  have hmFull : VDPLMultiIndex.weight m ≤ P.Slevel N :=
    hm.trans (P.Sstep_le_Slevel N)
  apply levelAlgebraicSourceRowError_le_exp_neg_three_quarters_of_closedForm
    P state b hb hbLastBound hbLast ((l : ℂ) / (P.q : ℂ)) m hmFull
      hfixed.1 hfixed.2.2.2.2.2
  · exact sourceSharpAlgebraicGrowthMajorant_le_integralDisk_structural_quarter
      P hreq N ht ((l : ℂ) / (P.q : ℂ)) hz
  · exact scaledAmplificationClosedForm_le_integralDisk_structural_quarter
      P hreq N ht ((l : ℂ) / (P.q : ℂ)) hz

/-- Actual pointwise comparison at a rational Lemma-5 target. -/
theorem norm_gSource_sub_fSource_ratCast_le_three_quarters
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    {N : ℕ} (state : LevelState P N) (b : Fin oldRank → ℤ)
    {bLast : ℤ} (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    {l : ℕ} (hl : l ≤ P.R (N + 1))
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep N)
    {C₀ : ℝ} (hfixed : HasFixedSourceConstantBounds P C₀)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ)))) :
    ‖gSource state b bLast ((l : ℂ) / (P.q : ℂ)) m -
        fSource state b bLast ((l : ℂ) / (P.q : ℂ)) m‖ ≤
      Real.exp (-3 * sourceExponent P
        (C₀ * Real.log P.OmegaOld) / 4) := by
  have hform := norm_logForm_le_smallLinearFormBound_of_normalized
    P C₀ b bLast hsmall
  exact (norm_gSource_sub_fSource_le_levelAlgebraicSourceRowError
    P state b hbLast ((l : ℂ) / (P.q : ℂ)) m
      (Real.exp_pos _).le hform).trans
        (levelAlgebraicSourceRowError_ratCast_le_three_quarters
          P hreq state b hb hbLastBound hbLast hl m hm hfixed)

/-- The terminal integral nodes used by Hermite interpolation satisfy the
same pointwise comparison bound, with the full Lemma-5 jet budget. -/
theorem norm_fSource_sub_gSource_terminalNode_le_three_quarters
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    {N : ℕ} (state : LevelState P N) (b : Fin oldRank → ℤ)
    {bLast : ℤ} (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    {C₀ : ℝ} (hfixed : HasFixedSourceConstantBounds P C₀)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (i : Fin (sourceRationalNodeRadius P N))
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ sourceRationalS P N) :
    ‖fSource state b bLast (((i.1 + 1 : ℕ) : ℂ)) m -
        gSource state b bLast (((i.1 + 1 : ℕ) : ℂ)) m‖ ≤
      Real.exp (-3 * sourceExponent P
        (C₀ * Real.log P.OmegaOld) / 4) := by
  have hform := norm_logForm_le_smallLinearFormBound_of_normalized
    P C₀ b bLast hsmall
  have hmFull : VDPLMultiIndex.weight m ≤ P.Slevel N := by
    exact hm.trans (by
      rw [sourceRationalS_eq_Slevel_div_six]
      exact Nat.div_le_self _ _)
  have hl : i.1 + 1 ≤
      P.lemmaFourRadius N (terminalPositiveStage P + 1) := by
    have hi : i.1 + 1 ≤ sourceRationalNodeRadius P N :=
      Nat.succ_le_iff.mpr i.2
    simpa only [sourceRationalNodeRadius, terminalPositiveStage_succ,
      terminalStage] using hi
  have hrow := levelAlgebraicSourceRowError_integralNode_le_three_quarters
    P hreq state b hb hbLastBound hbLast (terminalPositiveStage_lt P) hl
      m hmFull hfixed.1 hfixed.2.2.2.2.2
  rw [norm_sub_rev]
  exact (norm_gSource_sub_fSource_le_levelAlgebraicSourceRowError
    P state b hbLast (((i.1 + 1 : ℕ) : ℂ)) m
      (Real.exp_pos _).le hform).trans hrow

/-- Honest actual-auxiliary-function growth on the terminal Lemma-5 outer
circle.  The `24 H_t` term is the checked perturbation cost. -/
theorem norm_f_le_terminalRationalContour
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    {N : ℕ} (state : LevelState P N) (b : Fin oldRank → ℤ)
    {bLast : ℤ} (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    (hN : P.LevelOK N) {C₀ : ℝ}
    (hfixed : HasFixedSourceConstantBounds P C₀)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (m : VDPLMultiIndex P.rank)
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep N)
    (z : ℂ)
    (hz : z ∈ sphere (0 : ℂ)
      (3 * (sourceRationalNodeRadius P N : ℝ))) :
    ‖BakerSourceState.f state b bLast z m‖ ≤
      Real.exp (2 * sourceHeightUnit P +
        24 * positiveStageHeightUnit P
          (3 * (P.rank + 1) - 1)) := by
  have hzNorm : ‖z‖ = 3 * P.lemmaFourRadius N
      (terminalPositiveStage P + 1) := by
    rw [mem_sphere, dist_zero_right] at hz
    simpa only [sourceRationalNodeRadius, terminalPositiveStage_succ,
      terminalStage] using hz
  have hmTerminal : VDPLMultiIndex.weight m ≤
      P.lemmaFourBudget N (terminalPositiveStage P + 1) := by
    exact hm.trans (by
      simpa only [terminalPositiveStage_succ, terminalStage] using
        P.Sstep_le_terminalBudget hN)
  have hamp :=
    scaledAmplificationClosedForm_le_integralDisk_structural_quarter
      P hreq N (terminalPositiveStage_lt P) z (by rw [hzNorm])
  have hform := norm_logForm_le_smallLinearFormBound_of_normalized
    P C₀ b bLast hsmall
  simpa only [terminalPositiveStage] using
    norm_f_le_positiveContour P hreq state b hb hbLastBound hbLast
      (terminalPositiveStage P) z hzNorm m hmTerminal hfixed.1
        hfixed.2.2.2.2.2 hamp hform

/-- All analytic data needed by the exact rational Liouville lower
alternative are consequences of the source coefficient and constant
ledgers. -/
theorem algebraicRationalLowerInputs_of_sourceBounds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    {N : ℕ} (state : LevelState P N) (b : Fin oldRank → ℤ)
    {bLast : ℤ} (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    (hN : P.LevelOK N) {C₀ : ℝ}
    (hfixed : HasFixedSourceConstantBounds P C₀)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ)))) :
    AlgebraicRationalLowerInputs P state b bLast := by
  apply AlgebraicRationalLowerInputs.ofLevelScaledRowBound_of_sourceBounds
    hb hbLastBound hbLast hreq hN hfixed hsmall
  intro l _hl hlR m hm
  exact levelAlgebraicSourceRowError_ratCast_le_three_quarters
    P hreq state b hb hbLastBound hbLast hlR (toSourceMultiIndex P m)
      (by simpa only [weight_toSourceMultiIndex] using hm) hfixed

/-- Exact source Lemma 5 with every growth and pointwise comparison premise
discharged by the source majorant layer. -/
theorem rationalInterpolationUpperAtLevel_of_sourceBounds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    {N : ℕ} (state : LevelState P N) (b : Fin oldRank → ℤ)
    {bLast : ℤ} (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    (hN : P.LevelOK N)
    (hint : IntegralExtrapolatedAtLevel P
      (BakerSourceState.g state b bLast) N)
    {C₀ : ℝ} (hfixed : HasFixedSourceConstantBounds P C₀)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ)))) :
    RationalInterpolationUpperAtLevel P
      (BakerSourceState.f state b bLast)
      (fun l m ↦ stateRationalLiouvilleThreshold
        P N state b bLast l (toSourceMultiIndex P m)) N := by
  apply rationalInterpolationUpperAtLevel_of_source_exactLiouville
    state b hbLast hN hint hfixed.1 hfixed.2.1
      (P.exactRationalFixedHeight_requirement_of_fixedBounds hfixed)
  · intro i m hm
    exact norm_fSource_sub_gSource_terminalNode_le_three_quarters
      P hreq state b hb hbLastBound hbLast hfixed hsmall i m hm
  · intro _l _hl _hlR _hnmid m hm z hz
    exact norm_f_le_terminalRationalContour P hreq state b hb hbLastBound
      hbLast hN hfixed hsmall m hm z hz
  · intro l _hl hlR _hnmid m hm
    simpa only [rationalHeightScale, sourceHeightUnit] using
      levelAlgebraicGrowth_ratCast_le_exp_two P hreq state b bLast hb
        hbLastBound hlR (toSourceMultiIndex P m) (by
          simpa only [weight_toSourceMultiIndex] using hm)

end Erdos240.BakerSourceRationalAnalyticEndpoints

#print axioms
  Erdos240.BakerSourceRationalAnalyticEndpoints.levelAlgebraicSourceRowError_ratCast_le_three_quarters
#print axioms
  Erdos240.BakerSourceRationalAnalyticEndpoints.norm_fSource_sub_gSource_terminalNode_le_three_quarters
#print axioms
  Erdos240.BakerSourceRationalAnalyticEndpoints.norm_f_le_terminalRationalContour
#print axioms
  Erdos240.BakerSourceRationalAnalyticEndpoints.algebraicRationalLowerInputs_of_sourceBounds
#print axioms
  Erdos240.BakerSourceRationalAnalyticEndpoints.rationalInterpolationUpperAtLevel_of_sourceBounds
