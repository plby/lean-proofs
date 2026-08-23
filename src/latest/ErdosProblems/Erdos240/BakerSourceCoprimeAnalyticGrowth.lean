/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceCoprimeGridGrowth
import ErdosProblems.Erdos240.BakerSourceCoprimeAnalyticAbsorption

/-!
# Actual analytic growth on the p. 52 coprime circle

The algebraic source majorant on the successor circle costs `4 H / 3`.
The normalized logarithmic form makes the remaining perturbation exponent
at most one.  Since the fixed source-height unit is larger than `26 / 3`,
that unit fits in the remaining `H / 6` reserve.  This gives the actual
auxiliary-function estimate `exp (3 H / 2)` needed by coprime completion.
-/

noncomputable section

namespace Erdos240.BakerSourceCoprimeAnalyticGrowth

open Erdos240
open BakerLemma2Concrete
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerSourceAlgebraicUniformBounds
open BakerSourceCoprimeAnalyticAbsorption
open BakerSourceCoprimeGridGrowth
open BakerSourceMajorantClosedForm
open BakerSourcePositiveStageGrowth
open BakerSourceState

/-- The complete analytic closed form on the p. 52 successor circle costs
at most three halves of the fixed source-height unit. -/
theorem sourceSharpAnalyticGrowthMajorant_le_coprimeCircle
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    (J : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 4 * (P.R (J + 1) : ℝ))
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld)) :
    sourceSharpAnalyticGrowthMajorant P (J + 1) z (P.Sstep J)
        (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) ≤
      Real.exp ((3 / 2 : ℝ) * sourceHeightUnit P) := by
  have hgrowth :
      sourceSharpAlgebraicGrowthMajorant P (J + 1) z (P.Sstep J) ≤
        Real.exp ((4 / 3 : ℝ) * sourceHeightUnit P) := by
    exact sourceSharpAlgebraicGrowthMajorant_le_coprimeCircle
      P hreq J z hz
  exact analyticGrowth_le_exp_three_halves_of_coprimeBounds
    P J z hstruct hE hgrowth
      (scaledAmplificationClosedForm_le_structural_quarter P hreq J z hz)

/-- Actual auxiliary-function growth on the p. 52 successor circle, with
the full successor integral-seed budget.  No coefficient-dominance
hypothesis is used. -/
theorem norm_f_le_coprimeCircle_exp_three_halves
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    {J : ℕ} (state : LevelState P (J + 1))
    (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (z : ℂ) (hz : ‖z‖ = 4 * (P.R (J + 1) : ℝ))
    (m : VDPLMultiIndex P.rank)
    (hm : VDPLMultiIndex.weight m ≤ P.Slevel (J + 1)) :
    ‖f state b bLast z m‖ ≤
      Real.exp ((3 / 2 : ℝ) * sourceHeightUnit P) := by
  have hmStep : VDPLMultiIndex.weight m ≤ P.Sstep J :=
    hm.trans (P.Slevel_succ_le_Sstep J)
  have hzle : ‖z‖ ≤ 4 * (P.R (J + 1) : ℝ) := hz.le
  have hgrowth :
      sourceSharpAlgebraicGrowthMajorant P (J + 1) z (P.Sstep J) ≤
        Real.exp ((4 / 3 : ℝ) * sourceHeightUnit P) := by
    exact sourceSharpAlgebraicGrowthMajorant_le_coprimeCircle
      P hreq J z hzle
  exact norm_f_le_exp_three_halves_of_coprimeBounds
    P state b hb hbLastBound hbLast hstruct hE hsmall z m hmStep hgrowth
      (scaledAmplificationClosedForm_le_structural_quarter
        P hreq J z hzle)

end Erdos240.BakerSourceCoprimeAnalyticGrowth

#print axioms
  Erdos240.BakerSourceCoprimeAnalyticGrowth.sourceSharpAnalyticGrowthMajorant_le_coprimeCircle
#print axioms
  Erdos240.BakerSourceCoprimeAnalyticGrowth.norm_f_le_coprimeCircle_exp_three_halves
