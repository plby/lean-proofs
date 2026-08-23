/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAlgebraicMomentBounds

/-!
# Exponent bookkeeping for the algebraic source majorant

The source-faithful majorant for `g` is a product of four nonnegative
factors: support size, coefficient height, Delta size, and the algebraic
exponential.  This file isolates the elementary exponent bookkeeping which
turns separate exponential bounds for those factors into a single bound.

The same bookkeeping applies to the direct analytic envelope for `f`, with
one additional exponential factor coming from the small logarithmic form.
Keeping this step independent of the concrete Delta estimates lets the
integral, rational, and coprime-grid arguments share the exact same glue.
-/

noncomputable section

namespace Erdos240.BakerSourceAlgebraicExponentAbsorption

open Erdos240
open BakerLemma3
open BakerLemma3Concrete
open BakerSourceAlgebraicMajorant
open BakerSourceAlgebraicMomentBounds

namespace AlgebraicExponentialMajorant

variable
    {ι : Type*} [Fintype ι]
    {oldRank : ℕ} {I : Type*}
    {P : VDPLParameters ι} {coord : SourceCoordinates oldRank I}
    {support : Finset I} {p : I → ℤ}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {logAlpha : Fin oldRank → ℂ} {logAlphaLast : ℂ}
    {q N : ℕ} {z : ℂ} {m : VDPLMultiIndex (oldRank + 1)}
    {M : SourceMajorants P coord support p h b bLast logAlpha q N z m}

/-- Four separate exponential estimates multiply to the sum of their
exponents in the algebraic growth majorant. -/
theorem growth_le_exp_add_of_factor_bounds
    (A : AlgebraicExponentialMajorant P coord support p h b bLast
      logAlpha logAlphaLast q N z m M)
    {Esupport Ecoeff EDelta Erate : ℝ}
    (hsupport : M.supportMajorant ≤ Real.exp Esupport)
    (hcoeff : P.coeffHeight ≤ Real.exp Ecoeff)
    (hDelta : M.deltaMajorant ≤ Real.exp EDelta)
    (hrate : A.majorant ≤ Real.exp Erate) :
    A.growth ≤ Real.exp (Esupport + Ecoeff + EDelta + Erate) := by
  unfold BakerSourceAlgebraicMajorant.AlgebraicExponentialMajorant.growth
  have hcoeffDelta :
      P.coeffHeight * M.deltaMajorant ≤
        Real.exp Ecoeff * Real.exp EDelta :=
    mul_le_mul hcoeff hDelta M.deltaMajorant_nonneg
      (Real.exp_pos _).le
  have hsupportCoeffDelta :
      M.supportMajorant * (P.coeffHeight * M.deltaMajorant) ≤
        Real.exp Esupport * (Real.exp Ecoeff * Real.exp EDelta) :=
    mul_le_mul hsupport hcoeffDelta
      (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg)
      (Real.exp_pos _).le
  calc
    M.supportMajorant * (P.coeffHeight * M.deltaMajorant) * A.majorant ≤
        Real.exp Esupport * (Real.exp Ecoeff * Real.exp EDelta) *
          Real.exp Erate := by
      exact mul_le_mul hsupportCoeffDelta hrate A.majorant_nonneg
        (mul_nonneg (Real.exp_pos _).le
          (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
    _ = Real.exp (Esupport + Ecoeff + EDelta + Erate) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      ring

/-- Equal sixteenth-scale bounds for the four factors give the quarter-scale
growth estimate used by the concrete source inequalities. -/
theorem growth_le_exp_quarter_of_factor_bounds
    (A : AlgebraicExponentialMajorant P coord support p h b bLast
      logAlpha logAlphaLast q N z m M)
    {E : ℝ}
    (hsupport : M.supportMajorant ≤ Real.exp (E / 16))
    (hcoeff : P.coeffHeight ≤ Real.exp (E / 16))
    (hDelta : M.deltaMajorant ≤ Real.exp (E / 16))
    (hrate : A.majorant ≤ Real.exp (E / 16)) :
    A.growth ≤ Real.exp (E / 4) := by
  calc
    A.growth ≤
        Real.exp (E / 16 + E / 16 + E / 16 + E / 16) :=
      growth_le_exp_add_of_factor_bounds A hsupport hcoeff hDelta hrate
    _ = Real.exp (E / 4) := by
      congr 1
      ring

/-- Adding a bound for the perturbation exponent gives the corresponding
direct analytic-growth estimate for `f`. -/
theorem analyticGrowth_le_exp_add_of_factor_bounds
    (A : AlgebraicExponentialMajorant P coord support p h b bLast
      logAlpha logAlphaLast q N z m M)
    (linearFormBound : ℝ)
    {Esupport Ecoeff EDelta Erate Eperturbation : ℝ}
    (hsupport : M.supportMajorant ≤ Real.exp Esupport)
    (hcoeff : P.coeffHeight ≤ Real.exp Ecoeff)
    (hDelta : M.deltaMajorant ≤ Real.exp EDelta)
    (hrate : A.majorant ≤ Real.exp Erate)
    (hperturbation :
      M.amplificationMajorant * linearFormBound ≤ Eperturbation) :
    BakerSourceAlgebraicMomentBounds.AlgebraicExponentialMajorant.analyticGrowth
        A linearFormBound ≤
      Real.exp (Esupport + Ecoeff + EDelta + Erate + Eperturbation) := by
  have hgrowth :=
    growth_le_exp_add_of_factor_bounds A hsupport hcoeff hDelta hrate
  unfold BakerSourceAlgebraicMomentBounds.AlgebraicExponentialMajorant.analyticGrowth
  calc
    A.growth * Real.exp (M.amplificationMajorant * linearFormBound) ≤
        Real.exp (Esupport + Ecoeff + EDelta + Erate) *
          Real.exp Eperturbation := by
      exact mul_le_mul hgrowth (Real.exp_le_exp.mpr hperturbation)
        (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp
        (Esupport + Ecoeff + EDelta + Erate + Eperturbation) := by
      rw [← Real.exp_add]

/-- With all four algebraic factors and the perturbation exponent at scale
`E / 16`, the direct analytic envelope is at scale `5 * E / 16`. -/
theorem analyticGrowth_le_exp_five_sixteenths_of_factor_bounds
    (A : AlgebraicExponentialMajorant P coord support p h b bLast
      logAlpha logAlphaLast q N z m M)
    (linearFormBound : ℝ) {E : ℝ}
    (hsupport : M.supportMajorant ≤ Real.exp (E / 16))
    (hcoeff : P.coeffHeight ≤ Real.exp (E / 16))
    (hDelta : M.deltaMajorant ≤ Real.exp (E / 16))
    (hrate : A.majorant ≤ Real.exp (E / 16))
    (hperturbation :
      M.amplificationMajorant * linearFormBound ≤ E / 16) :
    BakerSourceAlgebraicMomentBounds.AlgebraicExponentialMajorant.analyticGrowth
        A linearFormBound ≤ Real.exp (5 * E / 16) := by
  calc
    BakerSourceAlgebraicMomentBounds.AlgebraicExponentialMajorant.analyticGrowth
        A linearFormBound ≤
        Real.exp (E / 16 + E / 16 + E / 16 + E / 16 + E / 16) :=
      analyticGrowth_le_exp_add_of_factor_bounds A linearFormBound
        hsupport hcoeff hDelta hrate hperturbation
    _ = Real.exp (5 * E / 16) := by
      congr 1
      ring

/-- A convenient half-scale weakening of the preceding exact estimate. -/
theorem analyticGrowth_le_exp_half_of_factor_bounds
    (A : AlgebraicExponentialMajorant P coord support p h b bLast
      logAlpha logAlphaLast q N z m M)
    (linearFormBound : ℝ) {E : ℝ} (hE : 0 ≤ E)
    (hsupport : M.supportMajorant ≤ Real.exp (E / 16))
    (hcoeff : P.coeffHeight ≤ Real.exp (E / 16))
    (hDelta : M.deltaMajorant ≤ Real.exp (E / 16))
    (hrate : A.majorant ≤ Real.exp (E / 16))
    (hperturbation :
      M.amplificationMajorant * linearFormBound ≤ E / 16) :
    BakerSourceAlgebraicMomentBounds.AlgebraicExponentialMajorant.analyticGrowth
        A linearFormBound ≤ Real.exp (E / 2) := by
  exact (analyticGrowth_le_exp_five_sixteenths_of_factor_bounds A
    linearFormBound hsupport hcoeff hDelta hrate hperturbation).trans
      (Real.exp_le_exp.mpr (by linarith))

/-- Direct consumer: the same five factor bounds give a half-scale bound
for the actual modified auxiliary function `f`. -/
theorem norm_vdplF_le_exp_half_of_factor_bounds
    (A : AlgebraicExponentialMajorant P coord support p h b bLast
      logAlpha logAlphaLast q N z m M)
    (hbLast : bLast ≠ 0) (linearFormBound : ℝ)
    (hbound : 0 ≤ linearFormBound)
    (hsmall :
      ‖logForm b bLast logAlpha logAlphaLast‖ ≤ linearFormBound)
    {E : ℝ} (hE : 0 ≤ E)
    (hsupport : M.supportMajorant ≤ Real.exp (E / 16))
    (hcoeff : P.coeffHeight ≤ Real.exp (E / 16))
    (hDelta : M.deltaMajorant ≤ Real.exp (E / 16))
    (hrate : A.majorant ≤ Real.exp (E / 16))
    (hperturbation :
      M.amplificationMajorant * linearFormBound ≤ E / 16) :
    ‖vdplF coord support p h b bLast logAlpha q N z m‖ ≤
      Real.exp (E / 2) :=
  (BakerSourceAlgebraicMomentBounds.AlgebraicExponentialMajorant.norm_vdplF_le_analyticGrowth
      A hbLast hbound hsmall).trans
    (analyticGrowth_le_exp_half_of_factor_bounds A linearFormBound hE
      hsupport hcoeff hDelta hrate hperturbation)

end AlgebraicExponentialMajorant

end Erdos240.BakerSourceAlgebraicExponentAbsorption

#print axioms
  Erdos240.BakerSourceAlgebraicExponentAbsorption.AlgebraicExponentialMajorant.growth_le_exp_quarter_of_factor_bounds
#print axioms
  Erdos240.BakerSourceAlgebraicExponentAbsorption.AlgebraicExponentialMajorant.analyticGrowth_le_exp_half_of_factor_bounds
#print axioms
  Erdos240.BakerSourceAlgebraicExponentAbsorption.AlgebraicExponentialMajorant.norm_vdplF_le_exp_half_of_factor_bounds
