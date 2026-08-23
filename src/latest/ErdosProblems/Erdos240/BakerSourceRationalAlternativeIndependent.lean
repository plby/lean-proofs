/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerLemma3Instantiation
import ErdosProblems.Erdos240.BakerInduction
import ErdosProblems.Erdos240.BakerSourceAlgebraicMomentBounds
import ErdosProblems.Erdos240.BakerSourceLiouvilleThresholds
import ErdosProblems.Erdos240.BakerSourceLogFormNormalization
import ErdosProblems.Erdos240.BakerSourceRationalFixedHeightBudget
import ErdosProblems.Erdos240.BakerSourceRationalGridGrowth

/-!
# Direct rational Liouville alternative for the level-scaled source majorant

The source function at level `J` scales the algebraic exponential rate by
`q⁻ʲ`, whereas the perturbation exponential is left unscaled.  Consequently
the sharp comparison estimate is expressed by `levelAlgebraicSourceRowError`,
not by the older unscaled `SourceMajorants.error` envelope.

This module separates the algebraic Liouville certificate from that analytic
comparison.  It reuses the fully checked rational-target integrality
certificate and accepts the actual norm comparison as its only premise.
-/

noncomputable section

namespace Erdos240.BakerSourceRationalAlternativeIndependent

open Erdos240
open Erdos240.BakerLemma3
open Erdos240.BakerLemma3Concrete
open Erdos240.BakerLemma3Instantiation
open Erdos240.BakerInduction
open Erdos240.BakerSourceAlgebraicLevelMajorant
open Erdos240.BakerSourceAlgebraicMomentBounds
open Erdos240.BakerSourceLogFormNormalization
open Erdos240.BakerSourceRationalLiouvilleLowerBounds
open Erdos240.BakerSourceRationalGridGrowth
open Erdos240.BakerSourcePositiveStageGrowth
open Erdos240.BakerSourceUniformConstantCompletion
open Erdos240.BakerSourceState

/-- The rational-target Liouville alternative driven directly by a norm
comparison.  This is the rational analogue of
`BakerSourceInnerPointwiseIndependent.state_integral_algebraicAlternative`.
No obsolete unscaled analytic majorant occurs in its type. -/
theorem state_rational_algebraicAlternative
    {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (l : ℕ) (m : VDPLMultiIndex (oldRank + 1))
    (hclose :
      ‖gSource state b bLast ((l : ℂ) / (P.q : ℂ)) m -
          fSource state b bLast ((l : ℂ) / (P.q : ℂ)) m‖ ≤
        stateRationalLiouvilleThreshold P J state b bLast l m) :
    gSource state b bLast ((l : ℂ) / (P.q : ℂ)) m = 0 ∨
      stateRationalLiouvilleThreshold P J state b bLast l m ≤
        ‖fSource state b bLast ((l : ℂ) / (P.q : ℂ)) m‖ := by
  change
    vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
        (oldLog P) (lastLog P) P.q J ((l : ℂ) / (P.q : ℂ)) m = 0 ∨
      stateRationalLiouvilleThreshold P J state b bLast l m ≤
        ‖vdplF (coordinatesForState state) state.support state.coeff P.h b
          bLast (oldLog P) P.q J ((l : ℂ) / (P.q : ℂ)) m‖
  change
    ‖vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
          (oldLog P) (lastLog P) P.q J ((l : ℂ) / (P.q : ℂ)) m -
        vdplF (coordinatesForState state) state.support state.coeff P.h b
          bLast (oldLog P) P.q J ((l : ℂ) / (P.q : ℂ)) m‖ ≤
      stateRationalLiouvilleThreshold P J state b bLast l m at hclose
  let A := stateRationalTargetCertificate P state b bLast l m
  have hclose' :
      ‖vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
            (oldLog P) (lastLog P) P.q J ((l : ℂ) / (P.q : ℂ)) m -
          vdplF (coordinatesForState state) state.support state.coeff P.h b
            bLast (oldLog P) P.q J ((l : ℂ) / (P.q : ℂ)) m‖ ≤
        ((A.conjugateBound ^
            (Module.finrank ℚ (SourceRadicalField P) - 1))⁻¹ /
          ‖A.scale‖) / 2 := by
    rw [A.finrank_eq_thirteen_pow]
    simpa [stateRationalLiouvilleThreshold, A,
      stateRationalTargetCertificate] using hclose
  have halt :=
    vdplG_eq_zero_or_half_lower_of_termwise_integral
      (coordinatesForState state) state.support state.coeff P.h b bLast
      (oldLog P) (lastLog P) P.q J ((l : ℂ) / (P.q : ℂ)) m
      A.term A.denominator A.sigma A.scale_ne A.denominator_map
      A.termIntegral A.term_map A.conjugateBound_pos A.other_embeddings
      hclose'
  rw [A.finrank_eq_thirteen_pow] at halt
  simpa [stateRationalLiouvilleThreshold, A,
    stateRationalTargetCertificate] using halt

/-! ## Assembly input with the literal sharp lower threshold -/

/-- The lower function used on the rational interpolation grid.  It is fixed
definitionally to the exact algebraic Liouville threshold, so the upper and
lower halves of Lemma 5 cannot accidentally be assembled with different
comparison constants. -/
def lower {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ) :
    ℕ → VDPLMultiIndex P.rank → ℝ :=
  fun l m ↦ stateRationalLiouvilleThreshold P J state b bLast l
    (toSourceMultiIndex P m)

/-- The source-faithful rational lower input.  Unlike the obsolete
`RationalLowerInputs`, this structure contains no unscaled source majorant:
its sole field is the exact alternative after the level-scaled analytic
comparison has been proved. -/
structure AlgebraicRationalLowerInputs {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ) where
  lowerStep : RationalLiouvilleAlternativeAtLevel P (f state b bLast)
    (g state b bLast) (lower P state b bLast) J

namespace AlgebraicRationalLowerInputs

variable {oldRank : ℕ} {P : VDPLParameters (Fin oldRank)} {J : ℕ}
  {state : LevelState P J} {b : Fin oldRank → ℤ} {bLast : ℤ}

/-- Package pointwise level-scaled comparison estimates into the precise
rational lower alternative consumed by the induction. -/
theorem ofClose
    (hclose : ∀ (l : ℕ), 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ (m : VDPLMultiIndex P.rank),
        VDPLMultiIndex.weight m ≤ P.Sstep J →
          ‖gSource state b bLast ((l : ℂ) / (P.q : ℂ))
                (toSourceMultiIndex P m) -
              fSource state b bLast ((l : ℂ) / (P.q : ℂ))
                (toSourceMultiIndex P m)‖ ≤
            stateRationalLiouvilleThreshold P J state b bLast l
              (toSourceMultiIndex P m)) :
    AlgebraicRationalLowerInputs P state b bLast where
  lowerStep := by
    intro l hl hlR m hm
    simpa only [lower, f, g] using
      state_rational_algebraicAlternative P state b bLast l
        (toSourceMultiIndex P m) (hclose l hl hlR m hm)

/-- Source-ready construction from the corrected level-scaled row error.
The same rational-grid growth estimate is passed to the exact-degree
Liouville lower bound, so no obsolete `exp (-3E/4)` lower threshold is
introduced. -/
theorem ofLevelScaledRowBounds [Nonempty (Fin oldRank)]
    {C₀ : ℝ} (hbLast : bLast ≠ 0)
    (hJ : P.LevelOK J)
    (hfixed : HasFixedSourceConstantBounds P C₀)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (hrow : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m : VDPLMultiIndex P.rank,
        VDPLMultiIndex.weight m ≤ P.Sstep J →
          levelAlgebraicSourceRowError P state b bLast
              ((l : ℂ) / (P.q : ℂ))
              (smallLinearFormBound P (C₀ * Real.log P.OmegaOld))
              (toSourceMultiIndex P m) ≤
            Real.exp (-3 * sourceExponent P
              (C₀ * Real.log P.OmegaOld) / 4))
    (hgrowth : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m : VDPLMultiIndex P.rank,
        VDPLMultiIndex.weight m ≤ P.Sstep J →
          (levelAlgebraicExponentialMajorant P state b bLast
            ((l : ℂ) / (P.q : ℂ))
              (toSourceMultiIndex P m)).growth ≤
            Real.exp (2 * rationalHeightScale P)) :
    AlgebraicRationalLowerInputs P state b bLast := by
  apply ofClose
  intro l hl hlR m hm
  have hform := norm_logForm_le_smallLinearFormBound_of_normalized
    P C₀ b bLast hsmall
  have hnorm :=
    norm_gSource_sub_fSource_le_levelAlgebraicSourceRowError
      P state b hbLast ((l : ℂ) / (P.q : ℂ))
        (toSourceMultiIndex P m) (Real.exp_pos _).le hform
  have hmSource :
      VDPLMultiIndex.weight (toSourceMultiIndex P m) ≤ P.Sstep J := by
    simpa only [weight_toSourceMultiIndex] using hm
  have hsum := P.hermite_add_outer_lt_stateRationalLiouvilleThreshold
    (J := J) (C₀ := C₀) hJ state b bLast hfixed l hlR
      (toSourceMultiIndex P m) hmSource
      (hgrowth l hl hlR m hm)
  have hE : 0 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld) :=
    le_trans (by norm_num) hfixed.2.2.2.2.2
  have hthreeSeven :
      Real.exp (-3 * sourceExponent P
          (C₀ * Real.log P.OmegaOld) / 4) ≤
        Real.exp (-7 * sourceExponent P
          (C₀ * Real.log P.OmegaOld) / 12) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact hnorm.trans ((hrow l hl hlR m hm).trans
    (hthreeSeven.trans ((le_add_of_nonneg_right (Real.exp_pos _).le).trans
      hsum.le)))

/-- Specialization of `ofLevelScaledRowBounds` in which the rational-grid
growth premise is discharged by the sharp closed source majorant.  The only
analytic input left is the corrected level-scaled row-error estimate. -/
theorem ofLevelScaledRowBound_of_sourceBounds [Nonempty (Fin oldRank)]
    {C₀ : ℝ} (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    (hreq : Erdos240.BakerLemma2Concrete.initialUnknownRequirement P ∈
      P.kRequirements)
    (hJ : P.LevelOK J)
    (hfixed : HasFixedSourceConstantBounds P C₀)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (hrow : ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
      ∀ m : VDPLMultiIndex P.rank,
        VDPLMultiIndex.weight m ≤ P.Sstep J →
          levelAlgebraicSourceRowError P state b bLast
              ((l : ℂ) / (P.q : ℂ))
              (smallLinearFormBound P (C₀ * Real.log P.OmegaOld))
              (toSourceMultiIndex P m) ≤
            Real.exp (-3 * sourceExponent P
              (C₀ * Real.log P.OmegaOld) / 4)) :
    AlgebraicRationalLowerInputs P state b bLast := by
  apply ofLevelScaledRowBounds hbLast hJ hfixed hsmall hrow
  intro l _hl hlR m hm
  simpa only [rationalHeightScale, sourceHeightUnit] using
    levelAlgebraicGrowth_ratCast_le_exp_two P hreq state b bLast hb
      hbLastBound hlR (toSourceMultiIndex P m) (by
        simpa only [weight_toSourceMultiIndex] using hm)

end AlgebraicRationalLowerInputs

end Erdos240.BakerSourceRationalAlternativeIndependent

#print axioms
  Erdos240.BakerSourceRationalAlternativeIndependent.state_rational_algebraicAlternative
#print axioms
  Erdos240.BakerSourceRationalAlternativeIndependent.AlgebraicRationalLowerInputs.ofClose
#print axioms
  Erdos240.BakerSourceRationalAlternativeIndependent.AlgebraicRationalLowerInputs.ofLevelScaledRowBounds
#print axioms
  Erdos240.BakerSourceRationalAlternativeIndependent.AlgebraicRationalLowerInputs.ofLevelScaledRowBound_of_sourceBounds
