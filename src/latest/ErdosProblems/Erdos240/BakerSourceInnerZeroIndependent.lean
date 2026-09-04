/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceInnerPointwiseIndependent
import ErdosProblems.Erdos240.BakerSourceInnerStepAssemblyIndependent
import ErdosProblems.Erdos240.BakerSourceLiouvilleLowerBounds
import ErdosProblems.Erdos240.BakerSourceLocalFixedHeightBudget
import ErdosProblems.Erdos240.BakerLemma4OuterEstimate

/-!
# The source Lemma-4 pointwise zero argument

This module combines the factorial-normalized current-rectangle jet bound,
the sharp local/outer equation-(9) estimate, and the integral Liouville
alternative.  Its hypotheses are the three pointwise majorant inequalities
which remain to be supplied by the closed-form source estimates; no global
Hasse-matrix or coefficient-dominance assumption is used.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceInnerZeroIndependent

open Erdos240
open Erdos240.BakerInduction
open Erdos240.BakerLemma3
open Erdos240.BakerLemma3Concrete
open Erdos240.BakerLemma3Instantiation
open Erdos240.BakerLemma4Concrete
open Erdos240.BakerLemma4InnerInduction
open Erdos240.BakerSourceAlgebraicMomentBounds
open Erdos240.BakerSourceInnerPointwiseIndependent
open Erdos240.BakerSourceInnerStepAssemblyIndependent
open Erdos240.BakerSourceLiouvilleLowerBounds
open Erdos240.BakerSourceLogFormNormalization
open Erdos240.BakerSourceOversizedConstantNumerics
open Erdos240.BakerSourceState

/-- A sharp equation-(9) estimate at one genuinely new integral target,
followed by the degree-one Liouville alternative, forces the source
auxiliary function to vanish there.

The local and outer terms are compared at the fixed height scale
`5 * h*k*Omega*log OmegaOld`.  Their sum is strictly below the integral
Liouville scale `4 * h*k*Omega*log OmegaOld`.  The comparison error at the
new target is stated directly with the algebraic (unmodified-rate)
majorant, so this theorem has no coefficient-dominance hypothesis. -/
theorem g_eq_zero_at_new_innerTarget_of_algebraicBounds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N t : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (hN : P.LevelOK N)
    (ht : t < terminalStage P)
    (hcurrent : InnerInvariant P (g state b bLast) N t)
    (C₀ : ℝ)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (hjet : jetAbsorptionConstant P ≤ C₀)
    (hrow : ∀
      (i : Fin (P.lemmaFourRadius N t))
      (m' : VDPLMultiIndex (oldRank + 1)),
      VDPLMultiIndex.weight m' ≤ P.Slevel N →
        levelAlgebraicSourceRowError P state b bLast
            ((i.1 + 1 : ℕ) : ℂ)
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) m' ≤
          Real.exp
            (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    {l : ℕ} (hnew : P.lemmaFourRadius N t < l)
    (hl : l ≤ P.lemmaFourRadius N (t + 1))
    (m : VDPLMultiIndex P.rank)
    (hm : VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1))
    {outer : ℝ} (houter : 0 ≤ outer)
    (hboundary : ∀ z : ℂ,
      ‖z‖ = 3 * (P.lemmaFourRadius N (t + 1) : ℝ) →
        ‖f state b bLast z m‖ ≤ outer)
    (hlocal :
      Real.exp
          (-(2 / 3) * sourceExponent P (C₀ * Real.log P.OmegaOld) +
            (P.lemmaFourContourAbsorptionConstant * (P.h : ℝ) *
              P.Omega * Real.log P.OmegaOld) / 6) ≤
        Real.exp (-(5 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld))))
    (hsharpOuter :
      (3 / 2 : ℝ) *
          ((1 / 3 : ℝ) ^
            (P.lemmaFourRadius N t *
              (P.lemmaFourBudget N t -
                P.lemmaFourBudget N (t + 1) + 1)) * outer) ≤
        Real.exp (-(5 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld))))
    (htargetError :
      levelAlgebraicSourceRowError P state b bLast (l : ℂ)
          (smallLinearFormBound P (C₀ * Real.log P.OmegaOld))
          (toSourceMultiIndex P m) ≤
        stateIntegralLiouvilleThreshold P N (toSourceMultiIndex P m)) :
    g state b bLast (l : ℂ) m = 0 := by
  let R := P.lemmaFourRadius N t
  let Rnext := P.lemmaFourRadius N (t + 1)
  let T := P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) + 1
  let E := sourceExponent P (C₀ * Real.log P.OmegaOld)
  let B := (P.lemmaFourContourAbsorptionConstant * (P.h : ℝ) *
    P.Omega * Real.log P.OmegaOld) / 6
  let H := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  have hR : 1 ≤ R := by
    exact Nat.one_le_iff_ne_zero.mpr (lemmaFourRadius_pos P N t).ne'
  have hRnext : 0 < Rnext := lemmaFourRadius_pos P N (t + 1)
  have hT : 1 ≤ T := by
    dsimp only [T]
    omega
  have hform := norm_logForm_le_smallLinearFormBound_of_normalized
    P C₀ b bLast hsmall
  have hjets : ∀ i : Fin R, ∀ j : Fin T,
      ‖iteratedDeriv j.1 (fun w ↦ f state b bLast w m)
          ((i.1 + 1 : ℕ) : ℂ) / (j.1.factorial : ℂ)‖ ≤
        Real.exp (-(2 / 3) * E) := by
    intro i j
    have hjetBound :=
      norm_normalizedIteratedDeriv_f_le_exp_neg_two_thirds_algebraic_of_currentInvariant
        state b hbLast hcurrent C₀ hsmall hjet
        (j := j.1)
        (show 1 ≤ i.1 + 1 by omega)
        (show i.1 + 1 ≤ R by omega) (hrow i) m
    have hj : j.1 ≤
        P.lemmaFourBudget N t - P.lemmaFourBudget N (t + 1) := by
      dsimp only [T] at j
      omega
    have hmj := weight_add_jet_le_currentBudget P N t m j.1 hm hj
    have hS := P.lemmaFourBudget_le_Slevel N t
    convert hjetBound hmj hS using 1 <;> dsimp only [E] <;> ring_nf
  have hcontour :
      (2 : ℝ) ^ (((3 * R + l) * T) + R * T) ≤ Real.exp B := by
    simpa only [R, Rnext, T, B] using
      P.lemmaFour_localCircleFactor_le_exp_sixth hN ht hl
  have hpoint : ‖f state b bLast (l : ℂ) m‖ < Real.exp (-(4 * H)) := by
    apply norm_entire_eval_lt_exp_neg_of_loss_and_sharpOuter
      hR hT hnew hRnext hl
      (differentiable_sourceState_f state b bLast m)
      (A := E) (B := B) (delta := Real.exp (-(2 / 3) * E))
      (outer := outer) (strong := 5 * H) (weak := 4 * H)
    · exact (Real.exp_pos _).le
    · exact houter
    · exact le_rfl
    · exact hcontour
    · exact hjets
    · exact hboundary
    · simpa only [E, B, H] using hlocal
    · simpa only [R, T, H] using hsharpOuter
    · have hH := P.one_le_sourceHeightUnit
      have hlog : Real.log 2 < 1 := by
        nlinarith [Real.log_two_lt_d9]
      dsimp only [H]
      linarith
  have hmSource :
      VDPLMultiIndex.weight (toSourceMultiIndex P m) ≤ P.Slevel N := by
    rw [weight_toSourceMultiIndex]
    exact hm.trans ((P.lemmaFourBudget_le_Slevel N (t + 1)))
  have hthreshold :=
    exp_neg_four_heightScale_lt_stateIntegralLiouvilleThreshold
      P hN (toSourceMultiIndex P m) hmSource
  have hclose :
      ‖gSource state b bLast (l : ℂ) (toSourceMultiIndex P m) -
          fSource state b bLast (l : ℂ) (toSourceMultiIndex P m)‖ ≤
        stateIntegralLiouvilleThreshold P N (toSourceMultiIndex P m) := by
    exact (norm_gSource_sub_fSource_le_levelAlgebraicSourceRowError
      P state b hbLast (l : ℂ) (toSourceMultiIndex P m)
        (by unfold smallLinearFormBound; positivity) hform).trans htargetError
  rcases state_integral_algebraicAlternative
      P state b bLast l (toSourceMultiIndex P m) hclose with hzero | hlower
  · simpa only [g, f, gSource, fSource] using hzero
  · exfalso
    exact (not_le_of_gt (hpoint.trans hthreshold)) hlower

/-- Assemble the complete inner Lemma-4 callback once the algebraic
closed-form estimates have supplied uniform node errors, boundary growth,
and new-target comparison errors.  All source numerical inequalities are
discharged here: the local loss uses the fixed-height absorption lemma, and
the sharp outer term is split into the exceptional `t = 0` estimate and the
uniform positive-stage estimate. -/
theorem innerStepCallback_of_algebraicGrowthBounds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (hN : P.LevelOK N)
    (C₀ : ℝ)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (hjet : jetAbsorptionConstant P ≤ C₀)
    (hcontour : 4 * P.lemmaFourContourAbsorptionConstant ≤ C₀)
    (hreq : P.sourceTenThreshold ∈ P.kRequirements)
    (outer : ℕ → VDPLMultiIndex P.rank → ℝ)
    (houter : ∀ t m, 0 ≤ outer t m)
    (hrow : ∀ (t : ℕ), t < terminalStage P →
      ∀ (i : Fin (P.lemmaFourRadius N t))
        (m' : VDPLMultiIndex (oldRank + 1)),
      VDPLMultiIndex.weight m' ≤ P.Slevel N →
        levelAlgebraicSourceRowError P state b bLast
            ((i.1 + 1 : ℕ) : ℂ)
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) m' ≤
          Real.exp
            (-3 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 4))
    (hboundary : ∀ (t : ℕ), t < terminalStage P →
      ∀ (m : VDPLMultiIndex P.rank),
      VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1) →
      ∀ z : ℂ, ‖z‖ = 3 * (P.lemmaFourRadius N (t + 1) : ℝ) →
        ‖f state b bLast z m‖ ≤ outer t m)
    (hzeroGrowth : ∀ (m : VDPLMultiIndex P.rank),
      VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N 1 →
        outer 0 m ≤ Real.exp
          (2 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)))
    (hpositiveGrowth : ∀ (t : ℕ), 1 ≤ t → t < terminalStage P →
      ∀ (m : VDPLMultiIndex P.rank),
      VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1) →
        outer t m ≤ Real.exp
          ((2 * (P.h : ℝ) * P.k + 24 * (P.h : ℝ) *
            P.k ^ (1 - P.sigma +
              P.epsilon * ((t + 1 : ℕ) : ℝ))) *
            (P.Omega * Real.log P.OmegaOld)))
    (htargetError : ∀ (t : ℕ), t < terminalStage P →
      ∀ (l : ℕ), P.lemmaFourRadius N t < l →
        l ≤ P.lemmaFourRadius N (t + 1) →
      ∀ (m : VDPLMultiIndex P.rank),
      VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1) →
        levelAlgebraicSourceRowError P state b bLast (l : ℂ)
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld))
            (toSourceMultiIndex P m) ≤
          stateIntegralLiouvilleThreshold P N (toSourceMultiIndex P m)) :
    InnerStepCallback P (g state b bLast) N := by
  apply innerStepCallback_of_pointwise P (g state b bLast) N
  intro t ht hcurrent l hl1 hl m hm
  by_cases hnew : P.lemmaFourRadius N t < l
  · apply g_eq_zero_at_new_innerTarget_of_algebraicBounds
      state b hbLast hN ht hcurrent C₀ hsmall hjet (hrow t ht)
      hnew hl m hm (houter t m) (hboundary t ht m hm)
    · exact Real.exp_le_exp.mpr
        (by
          convert P.localError_add_contourExponent_le_neg_five_sourceHeight
            hcontour using 1 <;> ring)
    · by_cases ht0 : t = 0
      · subst t
        exact (P.initial_threeHalves_mul_outerFactor_lt_exp_neg_five
          hN (houter 0 m) (hzeroGrowth m hm)).le
      · have htpos : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
        exact (P.positiveStage_threeHalves_mul_outerFactor_lt_exp_neg_five
          hN htpos ht hreq (houter t m)
            (hpositiveGrowth t htpos ht m hm)).le
    · exact htargetError t ht l hnew hl m hm
  · have hlold : l ≤ P.lemmaFourRadius N t := Nat.le_of_not_gt hnew
    have hmold : VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N t :=
      hm.trans (lemmaFourBudget_succ_le P N t)
    simpa only [Nat.cast_one, div_one] using hcurrent l hl1 hlold m hmold

end Erdos240.BakerSourceInnerZeroIndependent

#print axioms Erdos240.BakerSourceInnerZeroIndependent.g_eq_zero_at_new_innerTarget_of_algebraicBounds
#print axioms Erdos240.BakerSourceInnerZeroIndependent.innerStepCallback_of_algebraicGrowthBounds
