/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerCoprimeCompletion
import ErdosProblems.Erdos240.BakerCoprimeCompletionNumerics
import ErdosProblems.Erdos240.BakerCoprimeSharpIntegralLiouville
import ErdosProblems.Erdos240.BakerSourceInnerPointwiseIndependent

/-!
# Sharp p. 52 coprime completion

This file installs the exact numerical ledger into the coprime Hermite
completion.  The remaining hypotheses are the three literal analytic
estimates: the coprime-grid algebraic envelopes, the boundary numerator,
and the algebraic comparison row.  In particular the Hermite loss, nodal
product, strict Liouville comparison, and Liouville alternative are all
constructed internally.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerCoprimeCompletionSharp

open Complex Metric
open BakerCoprimeCertificateAssembly
open BakerCoprimeCompletion
open BakerCoprimeHermiteTarget
open BakerCoprimeInterpolation
open BakerCoprimeOuterEstimate
open BakerInduction
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerLemma4Concrete
open BakerSourceAlgebraicMajorant
open BakerSourceAlgebraicMomentBounds
open BakerSourceInnerPointwiseIndependent
open BakerSourceLogFormNormalization
open BakerSourceMomentCancellation
open BakerSourceOversizedConstantNumerics
open BakerSourceState
open HermiteInterpolation

/-- The complete p. 52 interpolation from the three source-faithful
analytic bounds.  All finite products and all strict numerical comparisons
are discharged in the proof. -/
theorem coprimeCompletionAtLevel_of_sharp_analytic_bounds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P (J + 1)) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (hJ : P.LevelOK (J + 1))
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hjet : jetAbsorptionConstant P ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (hgrowth : ∀ r ∈ coprimeNodeIndices P.q (P.R (J + 1)),
      ∀ m', VDPLMultiIndex.weight m' ≤ P.Sstep J →
        (scaledStateAlgebraicExponentialMajorant P state b bLast
          (((r + 1 : ℕ) : ℂ)) m').growth ≤
            Real.exp
              (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (hamplification : ∀ r ∈ coprimeNodeIndices P.q (P.R (J + 1)),
      ∀ m', VDPLMultiIndex.weight m' ≤ P.Sstep J →
        (stateSourceMajorants P state b bLast
          (((r + 1 : ℕ) : ℂ)) m').amplificationMajorant ≤
            Real.exp
              (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (hboundary : CoprimeDescentAtLevel P (g state b bLast) J →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Slevel (J + 1) →
      ∀ w, ‖w‖ = 4 * (P.R (J + 1) : ℝ) →
        ‖f state b bLast w m -
          (polynomial (fun z ↦ f state b bLast z m)
            (coprimeNodes P.q (P.R (J + 1)) (P.Sstep J / 4))).eval w‖ ≤
          Real.exp
            ((7 / 3 : ℝ) *
              ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)))
    (hrow : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Slevel (J + 1) →
        levelAlgebraicSourceRowError P state b bLast (l : ℂ)
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld))
            (toSourceMultiIndex P m) ≤
          Real.exp (-3 * sourceExponent P
            (C₀ * Real.log P.OmegaOld) / 4)) :
    CoprimeCompletionAtLevel P (g state b bLast) J := by
  let lower : ℕ → VDPLMultiIndex P.rank → ℝ := fun _l m ↦
    stateIntegralLiouvilleThreshold P (J + 1) (toSourceMultiIndex P m)
  have hpred : P.LevelOK J :=
    VDPLParameters.LevelOK.mono P hJ (Nat.le_succ J)
  intro hseed
  apply fill_integral_grid_of_coprime_certificates lower
  · intro l hl hlR hlcop m hm
    exact hseed l hl hlR hlcop m
      (hm.trans (P.Slevel_succ_le_Sstep J))
  · intro l hl hlR hlq m hm
    apply coprimeInterpolationCertificateOfBounds
      (q := P.q) (R := P.R (J + 1)) (T := P.Sstep J / 4) (l := l)
      (f := fun z ↦ f state b bLast z m)
      (polynomialBound :=
        Real.exp (-sourceExponent P (C₀ * Real.log P.OmegaOld) / 2))
      (outer := Real.exp
        ((7 / 3 : ℝ) *
          ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)))
      (decay := ((3 : ℝ)⁻¹ ^
        (P.R (J + 1) * (P.q - 1) / P.q)) ^ (P.Sstep J / 4))
      (lower := lower l m)
      (P.R_pos (J + 1)) (P.Sstep_div_four_pos_of_LevelOK hpred)
      hl hlR hlq (differentiable_sourceState_f state b bLast m)
      (hpoly0 := (Real.exp_pos _).le)
      (houter0 := (Real.exp_pos _).le)
      (hdecay0 := by positivity)
    · exact hboundary hseed m hm
    · exact norm_coprimeHermitePolynomial_eval_le_exp_neg_half
        state b hbLast hpred hseed hstruct hjet hE hsmall l hl hlR hlq
        hgrowth hamplification m hm
        (P.coprime_fullHermiteFactor_le_exp_sixth hpred hstruct)
    · intro w hw
      exact norm_successor_coprimeNodalProduct_div_le_source_factor
        P J l hlR hw
    · have hpoly :=
        P.exp_neg_half_sourceExponent_le_exp_neg_four_sourceHeight hstruct
      have houter :=
        P.four_thirds_mul_seven_thirds_growth_mul_coprime_decay_lt_exp_neg_thirtyFive_twelfths
          hpred (growth := Real.exp
            ((7 / 3 : ℝ) *
              ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) le_rfl
      exact (P.polynomial_add_outer_lt_exp_neg_five_halves_sourceHeight
          hpoly houter).trans
        (Erdos240.BakerCoprimeSharpIntegralLiouville.exp_neg_five_halves_heightScale_lt_successor_stateIntegralLiouvilleThreshold
            P hJ (toSourceMultiIndex P m) (by
              simpa only [weight_toSourceMultiIndex] using hm))
  · intro l hl hlR m hm
    change gSource state b bLast (l : ℂ) (toSourceMultiIndex P m) = 0 ∨
      stateIntegralLiouvilleThreshold P (J + 1)
          (toSourceMultiIndex P m) ≤
        ‖fSource state b bLast (l : ℂ) (toSourceMultiIndex P m)‖
    apply state_integral_algebraicAlternative
    have hform := norm_logForm_le_smallLinearFormBound_of_normalized
      P C₀ b bLast hsmall
    have hcompare :=
      norm_gSource_sub_fSource_le_levelAlgebraicSourceRowError
        P state b hbLast (l : ℂ) (toSourceMultiIndex P m)
        (by unfold smallLinearFormBound; positivity) hform
    have hheight :=
      P.eight_mul_sourceHeight_le_sourceExponent_of_structural hstruct
    have hHpos : 0 <
        (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld :=
      (by norm_num : (0 : ℝ) < 26 / 3).trans
        P.twentySix_thirds_lt_sourceHeightUnit
    have hexp : Real.exp (-3 * sourceExponent P
          (C₀ * Real.log P.OmegaOld) / 4) ≤
        Real.exp (-(6 *
          ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hscale : Real.exp (-(6 *
          ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) <
        Real.exp (-((5 / 2 : ℝ) *
          ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
      apply Real.exp_lt_exp.mpr
      nlinarith
    have hthreshold :=
      Erdos240.BakerCoprimeSharpIntegralLiouville.exp_neg_five_halves_heightScale_lt_successor_stateIntegralLiouvilleThreshold
        P hJ (toSourceMultiIndex P m) (by
          simpa only [weight_toSourceMultiIndex] using hm)
    exact hcompare.trans ((hrow l hl hlR m hm).trans
      (hexp.trans (hscale.trans hthreshold).le))

#print axioms coprimeCompletionAtLevel_of_sharp_analytic_bounds

end Erdos240.BakerCoprimeCompletionSharp
