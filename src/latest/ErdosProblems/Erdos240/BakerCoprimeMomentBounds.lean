/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAlgebraicMomentBounds

/-!
# Normalized source moments at the coprime nodes

The output of source Lemma 5 vanishes only at the positive nodes coprime to
`q`, but it retains the larger predecessor budget `Sstep J`.  This file
repeats the factorial-cancelled equation-(7)--(8) estimate with that exact
budget.  It is the analytic input to the second Hermite interpolation on
p. 52.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerCoprimeMomentBounds

open Erdos240
open BakerInduction
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerSourceAlgebraicMajorant
open BakerSourceAlgebraicMomentBounds
open BakerSourceLogFormNormalization
open BakerSourceMomentCancellation
open BakerSourceOversizedConstantNumerics
open BakerSourceState

/-! ## Absorbing the full predecessor `/9` budget -/

theorem Sstep_add_one_le_k_add_one_mul_normalizedCore {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) (J : ℕ) :
    (P.Sstep J + 1 : ℝ) ≤
      (P.k + 1) *
        (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld) := by
  have hS := P.Sstep_cast_le J
  have hscale := levelScale_le_k_mul_normalizedCore P J
  have hcore := one_le_normalizedCore P
  push_cast
  calc
    (P.Sstep J : ℝ) + 1 ≤
        P.k * (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld) +
          1 := by linarith
    _ ≤ P.k * (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld) +
          (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld) :=
      by linarith
    _ = (P.k + 1) *
        (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld) := by ring

theorem sourceJetCoefficientBound_Sstep_le_sourceExponent_div_twelve
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) :
    sourceJetCoefficientBound P (P.Sstep J) ≤
      sourceExponent P
        (jetAbsorptionConstant P * Real.log P.OmegaOld) / 12 := by
  have hside := Sstep_add_one_le_k_add_one_mul_normalizedCore P J
  have hmass : sourceJetCoefficientBound P (P.Sstep J) ≤
      ((P.k + 1) *
        (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld)) *
          oldJetFactor P := by
    unfold sourceJetCoefficientBound
    exact mul_le_mul_of_nonneg_right hside (oldJetFactor_nonneg P)
  calc
    sourceJetCoefficientBound P (P.Sstep J) ≤
        ((P.k + 1) *
          (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld)) *
            oldJetFactor P := hmass
    _ ≤ sourceExponent P
          (jetAbsorptionConstant P * Real.log P.OmegaOld) / 12 := by
      rw [sourceExponent_eq_normalized]
      unfold jetAbsorptionConstant
      have hlog : (1 : ℝ) ≤ Real.log P.Bsrc :=
        (show (1 : ℝ) ≤ 2 by norm_num).trans P.two_le_log_Bsrc
      have hfactor0 : 0 ≤ oldJetFactor P := oldJetFactor_nonneg P
      have hk1 : 0 ≤ P.k + 1 := by linarith [P.k_pos]
      have hprefix : 0 ≤
          12 * (P.k + 1) * oldJetFactor P * P.OmegaOld *
            Real.log P.OmegaOld * Real.log P.newHeight := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (by norm_num) hk1) hfactor0)
              P.OmegaOld_pos.le)
            P.log_OmegaOld_pos.le)
          P.log_newHeight_pos.le
      calc
        ((P.k + 1) *
            (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld)) *
              oldJetFactor P =
            (12 * (P.k + 1) * oldJetFactor P * P.OmegaOld *
              Real.log P.OmegaOld * Real.log P.newHeight * 1) / 12 := by
          ring
        _ ≤ (12 * (P.k + 1) * oldJetFactor P * P.OmegaOld *
              Real.log P.OmegaOld * Real.log P.newHeight *
                Real.log P.Bsrc) / 12 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog hprefix) (by norm_num)

theorem sourceJetCoefficientBound_Sstep_le_oversizedExponent_div_twelve
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) {C₀ : ℝ}
    (hC : jetAbsorptionConstant P ≤ C₀) :
    sourceJetCoefficientBound P (P.Sstep J) ≤
      sourceExponent P (C₀ * Real.log P.OmegaOld) / 12 := by
  calc
    sourceJetCoefficientBound P (P.Sstep J) ≤
        sourceExponent P
          (jetAbsorptionConstant P * Real.log P.OmegaOld) / 12 :=
      sourceJetCoefficientBound_Sstep_le_sourceExponent_div_twelve P J
    _ ≤ sourceExponent P (C₀ * Real.log P.OmegaOld) / 12 := by
      gcongr
      exact sourceExponent_mono_normalized P hC

theorem jetErrorIterate_Sstep_div_factorial_le_exp_neg_two_thirds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (J : ℕ)
    (bLast : ℤ) (hbLast : bLast ≠ 0) (j : ℕ)
    (Erow : VDPLMultiIndex (oldRank + 1) → ℝ)
    (hErow : ∀ m, 0 ≤ Erow m) {C₀ : ℝ}
    (hC : jetAbsorptionConstant P ≤ C₀)
    (hrow : ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
      Erow m ≤ Real.exp
        (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    (m : VDPLMultiIndex (oldRank + 1))
    (hmj : VDPLMultiIndex.weight m + j ≤ P.Sstep J) :
    jetErrorIterate P (J + 1) bLast j Erow m / ‖(j.factorial : ℂ)‖ ≤
      Real.exp
        (-2 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 3) := by
  let E := sourceExponent P (C₀ * Real.log P.OmegaOld)
  let delta := Real.exp (-3 * E / 4)
  have hdelta : 0 ≤ delta := (Real.exp_pos _).le
  have hiter := jetErrorIterate_div_factorial_le_exp_mul P (J + 1)
    bLast hbLast (P.Sstep J) j Erow hErow hdelta (by
      intro m' hm'
      simpa only [delta, E] using hrow m' hm') m hmj
  have hmass :=
    sourceJetCoefficientBound_Sstep_le_oversizedExponent_div_twelve
      P J hC
  calc
    jetErrorIterate P (J + 1) bLast j Erow m / ‖(j.factorial : ℂ)‖ ≤
        Real.exp (sourceJetCoefficientBound P (P.Sstep J)) * delta := hiter
    _ ≤ Real.exp (E / 12) * Real.exp (-3 * E / 4) := by
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hmass)
        (Real.exp_pos _).le
    _ = Real.exp (-2 * E / 3) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-! ## Equation-(8) at a coprime node -/

theorem norm_normalizedIteratedDeriv_f_le_algebraicSourceError_of_coprimeDescent
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P (J + 1)) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : CoprimeDescentAtLevel P (g state b bLast) J)
    (C₀ : ℝ)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    {l j : ℕ} (hl : 1 ≤ l) (hlR : l ≤ P.R (J + 1))
    (hlcop : l.Coprime P.q)
    (m : VDPLMultiIndex P.rank)
    (hmj : VDPLMultiIndex.weight m + j ≤ P.Sstep J) :
    ‖iteratedDeriv j (fun w ↦ f state b bLast w m) (l : ℂ) /
        (j.factorial : ℂ)‖ ≤
      jetErrorIterate P (J + 1) bLast j
          (levelAlgebraicSourceRowError P state b bLast (l : ℂ)
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
          (toSourceMultiIndex P m) /
        ‖(j.factorial : ℂ)‖ := by
  rw [normalizedIteratedDeriv_f_eq_jetIterate state b hbLast]
  have hzero : jetIterate P (J + 1) bLast j
      (fun m' ↦ gSource state b bLast (l : ℂ) m')
      (toSourceMultiIndex P m) = 0 := by
    apply jetIterate_eq_zero_of_weight P (J + 1) bLast _ (P.Sstep J) j
    · intro m' hm'
      have hz := hseed l hl hlR hlcop (fromSourceMultiIndex P m')
        (by simpa only [weight_fromSourceMultiIndex] using hm')
      simpa only [g, toSourceMultiIndex_fromSourceMultiIndex] using hz
    · simpa only [weight_toSourceMultiIndex] using hmj
  have hform := norm_logForm_le_smallLinearFormBound_of_normalized
    P C₀ b bLast hsmall
  have hdiff := norm_jetIterate_sub_le_of_weight P (J + 1) bLast
    (fun m' ↦ fSource state b bLast (l : ℂ) m')
    (fun m' ↦ gSource state b bLast (l : ℂ) m')
    (levelAlgebraicSourceRowError P state b bLast (l : ℂ)
      (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
    (P.Sstep J) j
    (by
      intro m'
      exact levelAlgebraicSourceRowError_nonneg P state b bLast (l : ℂ)
        (by unfold smallLinearFormBound; positivity) m')
    (by
      intro m' _hm'
      have hcomparison :=
        norm_gSource_sub_fSource_le_levelAlgebraicSourceRowError
          P state b hbLast
          (l : ℂ) m' (by unfold smallLinearFormBound; positivity) hform
      simpa only [norm_sub_rev] using hcomparison)
    (toSourceMultiIndex P m)
    (by simpa only [weight_toSourceMultiIndex] using hmj)
  rw [hzero, sub_zero] at hdiff
  rw [norm_div]
  exact div_le_div_of_nonneg_right hdiff (norm_nonneg _)

theorem norm_normalizedIteratedDeriv_f_le_exp_neg_two_thirds_of_coprimeDescent
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P (J + 1)) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : CoprimeDescentAtLevel P (g state b bLast) J)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hjet : jetAbsorptionConstant P ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (l j : ℕ) (hl : 1 ≤ l) (hlR : l ≤ P.R (J + 1))
    (hlcop : l.Coprime P.q)
    (hgrowth : ∀ m', VDPLMultiIndex.weight m' ≤ P.Sstep J →
      (scaledStateAlgebraicExponentialMajorant
        P state b bLast (l : ℂ) m').growth ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (hamplification : ∀ m', VDPLMultiIndex.weight m' ≤ P.Sstep J →
      (stateSourceMajorants P state b bLast (l : ℂ) m').amplificationMajorant ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (m : VDPLMultiIndex P.rank)
    (hmj : VDPLMultiIndex.weight m + j ≤ P.Sstep J) :
    ‖iteratedDeriv j (fun w ↦ f state b bLast w m) (l : ℂ) /
        (j.factorial : ℂ)‖ ≤
      Real.exp
        (-2 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 3) := by
  have hbase :=
    norm_normalizedIteratedDeriv_f_le_algebraicSourceError_of_coprimeDescent
      state b hbLast hseed C₀ hsmall hl hlR hlcop m hmj
  refine hbase.trans ?_
  apply jetErrorIterate_Sstep_div_factorial_le_exp_neg_two_thirds
    P J bLast hbLast j
    (levelAlgebraicSourceRowError P state b bLast (l : ℂ)
      (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
  · intro m'
    exact levelAlgebraicSourceRowError_nonneg P state b bLast (l : ℂ)
      (by unfold smallLinearFormBound; positivity) m'
  · exact hjet
  · intro m' hm'
    exact algebraicError_le_exp_neg_three_quarters_of_oversized
      (scaledStateAlgebraicExponentialMajorant
        P state b bLast (l : ℂ) m')
      hstruct hE (hgrowth m' hm') (hamplification m' hm')
  · simpa only [weight_toSourceMultiIndex] using hmj

#print axioms Sstep_add_one_le_k_add_one_mul_normalizedCore
#print axioms sourceJetCoefficientBound_Sstep_le_oversizedExponent_div_twelve
#print axioms jetErrorIterate_Sstep_div_factorial_le_exp_neg_two_thirds
#print axioms norm_normalizedIteratedDeriv_f_le_algebraicSourceError_of_coprimeDescent
#print axioms norm_normalizedIteratedDeriv_f_le_exp_neg_two_thirds_of_coprimeDescent

end Erdos240.BakerCoprimeMomentBounds
