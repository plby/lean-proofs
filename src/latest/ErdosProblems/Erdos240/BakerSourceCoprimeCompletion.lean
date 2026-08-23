/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceCoprimeAnalyticGrowth
import ErdosProblems.Erdos240.BakerSourceUniformConstantCompletion

/-!
# Unconditional source p. 52 coprime completion

This file combines the closed source majorants, the descent-dependent
coprime Hermite boundary estimate, and the sharp Liouville ledger.  Its
main theorem has no analytic certificates: one fixed-family source
constant supplies every numerical hypothesis.
-/

noncomputable section

namespace Erdos240.BakerSourceCoprimeCompletion

open Erdos240
open BakerCoprimeCompletionSharp
open BakerCoprimeInterpolation
open BakerInduction
open BakerLemma2Concrete
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerSourceCoprimeAnalyticGrowth
open BakerSourceCoprimeGridGrowth
open BakerSourceOversizedConstantNumerics
open BakerSourceState
open BakerSourceUniformConstantCompletion
open HermiteInterpolation

/-- Complete p. 52 coprime-node interpolation from the literal source
bounds.  Every analytic growth, jet, Hermite, product, and Liouville
obligation is discharged internally. -/
theorem coprimeCompletionAtLevel_of_sourceBounds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    {J : ℕ} (state : LevelState P (J + 1))
    (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    (hnext : P.LevelOK (J + 1))
    {C₀ : ℝ} (hfixed : HasFixedSourceConstantBounds P C₀)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ)))) :
    CoprimeCompletionAtLevel P (g state b bLast) J := by
  have hpred : P.LevelOK J :=
    VDPLParameters.LevelOK.mono P hnext (Nat.le_succ J)
  have hstruct : 4 * P.C ≤ C₀ := hfixed.1
  have hjet : jetAbsorptionConstant P ≤ C₀ := hfixed.2.1
  have hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld) :=
    hfixed.2.2.2.2.2
  apply coprimeCompletionAtLevel_of_sharp_analytic_bounds
    state b hbLast hnext hstruct hjet hE hsmall
  · intro r hr m hm
    exact coprimeNode_algebraicGrowth_le_structural_quarter
      state b bLast hb hbLastBound hreq r hr m hm
  · intro r hr m _hm
    exact coprimeNode_amplification_le_structural_quarter
      state b hbLast hreq r hr m
  · intro hseed m hm w hw
    calc
      ‖f state b bLast w m -
          (polynomial (fun z ↦ f state b bLast z m)
            (coprimeNodes P.q (P.R (J + 1)) (P.Sstep J / 4))).eval w‖ ≤
        ‖f state b bLast w m‖ +
          ‖(polynomial (fun z ↦ f state b bLast z m)
            (coprimeNodes P.q (P.R (J + 1)) (P.Sstep J / 4))).eval w‖ :=
        norm_sub_le _ _
      _ ≤ Real.exp ((3 / 2 : ℝ) *
            ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) +
          Real.exp (-sourceExponent P
            (C₀ * Real.log P.OmegaOld) / 2) := by
        exact add_le_add
          (norm_f_le_coprimeCircle_exp_three_halves
            P hreq state b hb hbLastBound hbLast hstruct hE hsmall w hw m hm)
          (norm_coprimeHermitePolynomial_boundary_le_exp_neg_half
            state b hb hbLastBound hbLast hreq hpred hseed hstruct hjet hE
              hsmall m hm w hw)
      _ ≤ Real.exp ((3 / 2 : ℝ) *
            ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) +
          Real.exp (-(4 *
            ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) := by
        exact add_le_add le_rfl
          (P.exp_neg_half_sourceExponent_le_exp_neg_four_sourceHeight
            hstruct)
      _ ≤ Real.exp ((7 / 3 : ℝ) *
          ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) :=
        P.exp_three_halves_add_exp_neg_four_le_exp_seven_thirds
  · intro l _hl hlR m hm
    exact integralTarget_rowError_le_exp_neg_three_quarters
      state b hb hbLastBound hbLast hreq hstruct hE l hlR m hm

end Erdos240.BakerSourceCoprimeCompletion

#print axioms
  Erdos240.BakerSourceCoprimeCompletion.coprimeCompletionAtLevel_of_sourceBounds
