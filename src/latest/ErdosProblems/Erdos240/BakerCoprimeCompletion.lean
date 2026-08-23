/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerCoprimeCertificateAssembly
import ErdosProblems.Erdos240.BakerSourceNumericalAssemblyIndependent

/-!
# Concrete p. 52 coprime completion

This is the certificate-free completion interface.  The algebraic
Liouville alternative is produced internally by instantiated source Lemma 3;
the remaining hypotheses are pointwise analytic majorants and explicit
parameter inequalities.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerCoprimeCompletion

open Complex Metric
open BakerCoprimeCertificateAssembly
open BakerCoprimeHermiteTarget
open BakerCoprimeInterpolation
open BakerCoprimeOuterEstimate
open BakerInduction
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerLemma4Concrete
open BakerSourceAlgebraicMajorant
open BakerSourceAlgebraicMomentBounds
open BakerSourceLogFormNormalization
open BakerSourceMomentCancellation
open BakerSourceNumericalAssemblyIndependent
open BakerSourceOversizedConstantNumerics
open BakerSourceState
open HermiteInterpolation

/-- Source Lemma 3 supplies the exact integral-target Liouville alternative
needed by the completion.  No algebraic certificate remains in the type. -/
theorem integral_liouville_alternative_of_error
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (l : ℕ) (m : VDPLMultiIndex P.rank)
    (herror :
      (stateSourceMajorants P state b bLast (l : ℂ)
        (toSourceMultiIndex P m)).error
          (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) ≤
        stateIntegralLiouvilleThreshold P J (toSourceMultiIndex P m)) :
    g state b bLast (l : ℂ) m = 0 ∨
      stateIntegralLiouvilleThreshold P J (toSourceMultiIndex P m) ≤
        ‖f state b bLast (l : ℂ) m‖ := by
  let B := integralNumericalConditionsOfError P state b bLast C₀ hC₀ l m herror
  have hform := norm_logForm_le_smallLinearFormBound_of_normalized
    P C₀ b bLast hsmall
  have hlemma := quantitative_lemma3_state_integral P state b bLast l
    (toSourceMultiIndex P m) B hbLast (by
      simpa only [B, integralNumericalConditionsOfError_sourceConstant] using
        hform) (by
      rw [integralNumericalConditionsOfError_errorEnvelope])
  change gSource state b bLast (l : ℂ) (toSourceMultiIndex P m) = 0 ∨
    stateIntegralLiouvilleThreshold P J (toSourceMultiIndex P m) ≤
      ‖fSource state b bLast (l : ℂ) (toSourceMultiIndex P m)‖
  change BakerLemma3.vdplG (coordinatesForState state) state.support
      state.coeff P.h b bLast (oldLog P) (lastLog P) P.q J (l : ℂ)
        (toSourceMultiIndex P m) = 0 ∨
    stateIntegralLiouvilleThreshold P J (toSourceMultiIndex P m) ≤
      ‖BakerLemma3.vdplF (coordinatesForState state) state.support
        state.coeff P.h b bLast (oldLog P) P.q J (l : ℂ)
          (toSourceMultiIndex P m)‖
  exact hlemma.2.2

/-- Completion from explicit source bounds.  In contrast with the earlier
certificate adapter, this theorem constructs every Hermite certificate and
every Lemma-3 Liouville alternative internally. -/
theorem coprimeCompletionAtLevel_of_explicit_bounds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P (J + 1)) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (hJ : P.LevelOK J)
    {C₀ : ℝ} (hC₀ : 0 < C₀) (hstruct : 4 * P.C ≤ C₀)
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
    (hhermiteLoss :
      ((coprimeNodeIndices P.q (P.R (J + 1))).card : ℝ) *
          ((P.Sstep J / 4 : ℕ) : ℝ) *
          ((P.Sstep J / 4 : ℕ) : ℝ) *
        (((P.q : ℝ) * (2 : ℝ) ^ (3 * P.R (J + 1))) ^
            (P.Sstep J / 4) *
          (2 : ℝ) ^
            ((coprimeNodeIndices P.q (P.R (J + 1))).card *
                (P.Sstep J / 4) + (P.Sstep J / 4))) ≤
        Real.exp
          (sourceExponent P (C₀ * Real.log P.OmegaOld) / 6))
    (hboundary : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) → ¬l.Coprime P.q →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Slevel (J + 1) →
      ∀ w, ‖w‖ = 4 * (P.R (J + 1) : ℝ) →
        ‖f state b bLast w m -
          (polynomial (fun z ↦ f state b bLast z m)
            (coprimeNodes P.q (P.R (J + 1)) (P.Sstep J / 4))).eval w‖ ≤
          Real.exp
            (2 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)))
    (hstrict : ∀ m, VDPLMultiIndex.weight m ≤ P.Slevel (J + 1) →
      Real.exp
          (-sourceExponent P (C₀ * Real.log P.OmegaOld) / 2) +
        (4 / 3 : ℝ) *
          Real.exp
            (2 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) *
          (((3 : ℝ)⁻¹ ^
            (P.R (J + 1) * (P.q - 1) / P.q)) ^ (P.Sstep J / 4)) <
        stateIntegralLiouvilleThreshold P (J + 1)
          (toSourceMultiIndex P m))
    (herror : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m, VDPLMultiIndex.weight m ≤ P.Slevel (J + 1) →
        (stateSourceMajorants P state b bLast (l : ℂ)
          (toSourceMultiIndex P m)).error
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) ≤
          stateIntegralLiouvilleThreshold P (J + 1)
            (toSourceMultiIndex P m)) :
    CoprimeCompletionAtLevel P (g state b bLast) J := by
  let lower : ℕ → VDPLMultiIndex P.rank → ℝ := fun _l m ↦
    stateIntegralLiouvilleThreshold P (J + 1) (toSourceMultiIndex P m)
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
      (outer :=
        Real.exp (2 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)))
      (decay := ((3 : ℝ)⁻¹ ^ (P.R (J + 1) * (P.q - 1) / P.q)) ^
        (P.Sstep J / 4))
      (lower := lower l m)
      (P.R_pos (J + 1)) (P.Sstep_div_four_pos_of_LevelOK hJ)
      hl hlR hlq (differentiable_sourceState_f state b bLast m)
      (hpoly0 := (Real.exp_pos _).le)
      (houter0 := (Real.exp_pos _).le)
      (hdecay0 := by positivity)
    · exact hboundary l hl hlR hlq m hm
    · exact norm_coprimeHermitePolynomial_eval_le_exp_neg_half
        state b hbLast hJ hseed hstruct hjet hE hsmall l hl hlR hlq
        hgrowth hamplification m hm hhermiteLoss
    · intro w hw
      exact norm_successor_coprimeNodalProduct_div_le_source_factor
        P J l hlR hw
    · exact hstrict m hm
  · intro l hl hlR m hm
    exact integral_liouville_alternative_of_error state b hbLast hC₀ hsmall
      l m (herror l hl hlR m hm)

#print axioms integral_liouville_alternative_of_error
#print axioms coprimeCompletionAtLevel_of_explicit_bounds

end Erdos240.BakerCoprimeCompletion
