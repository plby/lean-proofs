/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAlgebraicMajorant
import ErdosProblems.Erdos240.BakerSourceMomentCancellation
import ErdosProblems.Erdos240.BakerSourceOversizedConstantNumerics

/-!
# Algebraic-base growth and source moment cancellation

`BakerSourceAlgebraicMajorant` contains the canonical source-faithful
majorant: the unmodified algebraic function `g` is bounded first, and `f`
is recovered through the small perturbation.  This file supplies two
downstream endpoints:

* the sharper direct bound `‖f‖ ≤ growth(g) * exp(amplification * ‖Λ‖)`;
* equation-(8) moment cancellation with the algebraic comparison error.

Neither endpoint assumes that the last logarithmic-form coefficient
dominates the other coefficients.  The only coefficient assumption is
`bLast ≠ 0`, exactly as in the source.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceAlgebraicMomentBounds

open Finset
open Erdos240
open BakerInduction
open BakerLemma3
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerSourceAlgebraicMajorant
open BakerSourceAlgebraicMajorant.AlgebraicExponentialMajorant
open BakerSourceLogFormNormalization
open BakerSourceMomentCancellation
open BakerSourceOversizedConstantNumerics
open BakerSourceState

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

/-- The sharper analytic growth envelope obtained by using the exact
termwise factorization of `f` through the unmodified algebraic terms. -/
def analyticGrowth
    (A : AlgebraicExponentialMajorant P coord support p h b bLast
      logAlpha logAlphaLast q N z m M)
    (linearFormBound : ℝ) : ℝ :=
  A.growth * Real.exp (M.amplificationMajorant * linearFormBound)

theorem analyticGrowth_nonneg
    (A : AlgebraicExponentialMajorant P coord support p h b bLast
      logAlpha logAlphaLast q N z m M)
    (linearFormBound : ℝ) : 0 ≤ analyticGrowth A linearFormBound := by
  unfold analyticGrowth growth
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg M.supportMajorant_nonneg
        (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg))
      A.majorant_nonneg)
    (Real.exp_pos _).le

/-- Direct source-faithful growth of `f`.  This is stronger than recovering
`f` by a triangle inequality from `g` and `g-f`. -/
theorem norm_vdplF_le_analyticGrowth
    (A : AlgebraicExponentialMajorant P coord support p h b bLast
      logAlpha logAlphaLast q N z m M)
    (hbLast : bLast ≠ 0) {linearFormBound : ℝ}
    (hbound : 0 ≤ linearFormBound)
    (hsmall : ‖logForm b bLast logAlpha logAlphaLast‖ ≤ linearFormBound) :
    ‖vdplF coord support p h b bLast logAlpha q N z m‖ ≤
      analyticGrowth A linearFormBound := by
  rw [vdplF_eq_sum]
  refine (norm_sum_le _ _).trans ?_
  let perturbationBound := M.amplificationMajorant * linearFormBound
  calc
    ∑ lambda ∈ support,
        ‖sourceCoefficient coord p h b bLast q N z m lambda *
          Complex.exp (modifiedRate coord b bLast logAlpha lambda * z)‖ ≤
        ∑ _lambda ∈ support,
          (P.coeffHeight * M.deltaMajorant) * A.majorant *
            Real.exp perturbationBound := by
      apply sum_le_sum
      intro lambda hlambda
      have hfactor :=
        BakerSourceAlgebraicMajorant.AlgebraicExponentialMajorant.sourceTerm_modified_eq_algebraic_mul_exp_neg_perturbation
          (coord := coord) (p := p) (h := h) (b := b) (bLast := bLast)
          (logAlpha := logAlpha) (logAlphaLast := logAlphaLast)
          (q := q) (N := N) (z := z) (m := m) hbLast lambda
      rw [hfactor, norm_mul, norm_mul]
      have hperturbation :
          ‖perturbationRate coord b bLast logAlpha logAlphaLast lambda * z‖ ≤
            perturbationBound := by
        calc
          ‖perturbationRate coord b bLast logAlpha logAlphaLast lambda * z‖ ≤
              ‖(coord.lastExponent lambda : ℂ) / (bLast : ℂ)‖ *
                linearFormBound * ‖z‖ :=
            norm_perturbationRate_mul_le_of_logForm coord b bLast logAlpha
              logAlphaLast lambda z hsmall
          _ = (‖(coord.lastExponent lambda : ℂ) / (bLast : ℂ)‖ * ‖z‖) *
                linearFormBound := by ring
          _ ≤ perturbationBound :=
            mul_le_mul_of_nonneg_right (M.amplification_le lambda hlambda) hbound
      have halgebraicExp :
          ‖Complex.exp
            (algebraicRate coord logAlpha logAlphaLast lambda * z)‖ ≤
              A.majorant := by
        calc
          ‖Complex.exp
              (algebraicRate coord logAlpha logAlphaLast lambda * z)‖ ≤
              Real.exp
                ‖algebraicRate coord logAlpha logAlphaLast lambda * z‖ :=
            Complex.norm_exp_le_exp_norm _
          _ ≤ Real.exp
              (‖algebraicRate coord logAlpha logAlphaLast lambda‖ * ‖z‖) :=
            Real.exp_le_exp.mpr (norm_mul_le _ _)
          _ ≤ A.majorant := A.exponential_le lambda hlambda
      have hnegativeExp :
          ‖Complex.exp
            (-(perturbationRate coord b bLast logAlpha logAlphaLast lambda * z))‖ ≤
              Real.exp perturbationBound := by
        calc
          ‖Complex.exp
              (-(perturbationRate coord b bLast logAlpha logAlphaLast lambda * z))‖ ≤
              Real.exp
                ‖-(perturbationRate coord b bLast logAlpha logAlphaLast lambda * z)‖ :=
            Complex.norm_exp_le_exp_norm _
          _ = Real.exp
              ‖perturbationRate coord b bLast logAlpha logAlphaLast lambda * z‖ := by
            rw [norm_neg]
          _ ≤ Real.exp perturbationBound := Real.exp_le_exp.mpr hperturbation
      exact mul_le_mul
        (mul_le_mul (M.sourceCoefficient_le hlambda) halgebraicExp
          (norm_nonneg _)
          (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg))
        hnegativeExp (norm_nonneg _)
        (mul_nonneg
          (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg)
          A.majorant_nonneg)
    _ = (support.card : ℝ) *
          (((P.coeffHeight * M.deltaMajorant) * A.majorant) *
            Real.exp perturbationBound) := by simp
    _ ≤ M.supportMajorant *
          (((P.coeffHeight * M.deltaMajorant) * A.majorant) *
            Real.exp perturbationBound) := by
      exact mul_le_mul_of_nonneg_right M.support_card_le
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg)
            A.majorant_nonneg)
          (Real.exp_pos _).le)
    _ = analyticGrowth A linearFormBound := by
      simp only [analyticGrowth, growth]
      dsimp only [perturbationBound]
      ring

end AlgebraicExponentialMajorant

/-! ## Corrected source-state consumers -/

/-- An old source exponent at level `N` retains its exact `q ^ (-N)`
scale.  This estimate lives here so every row-error consumer uses the
scaled algebraic base. -/
theorem scaledState_oldExponent_cast_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {N : ℕ}
    (state : LevelState P N) (lambda : LevelIndex P N) (r : Fin oldRank) :
    ((coordinatesForState state).oldExponent lambda r : ℝ) ≤
      P.qInvPow N * (P.LiZero r : ℝ) := by
  calc
    ((coordinatesForState state).oldExponent lambda r : ℝ) ≤
        ((levelBoxShape P N).oldMax r : ℕ) := by
      exact_mod_cast Nat.le_of_lt_succ (lambda.oldExponentFin r).isLt
    _ = (scaledExponentMax P N (P.LiZero r) : ℕ) := rfl
    _ ≤ P.qInvPow N * (P.LiZero r : ℝ) :=
      scaledExponentMax_cast_le P N (P.LiZero r)

/-- The last source exponent has the same exact level scale. -/
theorem scaledState_lastExponent_cast_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {N : ℕ}
    (state : LevelState P N) (lambda : LevelIndex P N) :
    ((coordinatesForState state).lastExponent lambda : ℝ) ≤
      P.qInvPow N * (P.LlastZero : ℝ) := by
  calc
    ((coordinatesForState state).lastExponent lambda : ℝ) ≤
        ((levelBoxShape P N).lastMax : ℕ) := by
      exact_mod_cast Nat.le_of_lt_succ lambda.lastExponentFin.isLt
    _ = (scaledExponentMax P N P.LlastZero : ℕ) := rfl
    _ ≤ P.qInvPow N * (P.LlastZero : ℝ) :=
      scaledExponentMax_cast_le P N P.LlastZero

/-- The algebraic exponential rate, with the level factor retained. -/
theorem norm_scaledState_algebraicRate_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {N : ℕ}
    (state : LevelState P N) (lambda : LevelIndex P N) :
    ‖algebraicRate (coordinatesForState state) (oldLog P) (lastLog P) lambda‖ ≤
      P.qInvPow N * sourceAlgebraicRateBound P := by
  unfold algebraicRate sourceAlgebraicRateBound
  calc
    ‖(∑ r,
          ((coordinatesForState state).oldExponent lambda r : ℂ) * oldLog P r) +
        ((coordinatesForState state).lastExponent lambda : ℂ) * lastLog P‖ ≤
        ‖∑ r,
          ((coordinatesForState state).oldExponent lambda r : ℂ) * oldLog P r‖ +
          ‖((coordinatesForState state).lastExponent lambda : ℂ) * lastLog P‖ :=
      norm_add_le _ _
    _ ≤ (∑ r,
          ‖((coordinatesForState state).oldExponent lambda r : ℂ) * oldLog P r‖) +
          ‖((coordinatesForState state).lastExponent lambda : ℂ) * lastLog P‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (∑ r,
          (P.qInvPow N * (P.LiZero r : ℝ)) * ‖oldLog P r‖) +
          (P.qInvPow N * (P.LlastZero : ℝ)) * ‖lastLog P‖ := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro r _hr
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right
          (scaledState_oldExponent_cast_le P state lambda r) (norm_nonneg _)
      · rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right
          (scaledState_lastExponent_cast_le P state lambda) (norm_nonneg _)
    _ = P.qInvPow N *
          ((∑ r, (P.LiZero r : ℝ) * ‖oldLog P r‖) +
            (P.LlastZero : ℝ) * ‖lastLog P‖) := by
      rw [mul_add, Finset.mul_sum]
      ring_nf

/-- Canonical level-scaled algebraic exponential majorant used both for
pointwise row errors and analytic growth. -/
def scaledStateAlgebraicExponentialMajorant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {N : ℕ} (state : LevelState P N)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    AlgebraicExponentialMajorant P (coordinatesForState state) state.support
      state.coeff P.h b bLast (oldLog P) (lastLog P) P.q N z m
      (stateSourceMajorants P state b bLast z m) where
  majorant := Real.exp (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖)
  majorant_nonneg := (Real.exp_pos _).le
  exponential_le := by
    intro lambda _hlambda
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (norm_scaledState_algebraicRate_le P state lambda) (norm_nonneg z))

@[simp] theorem scaledStateAlgebraicExponentialMajorant_majorant
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) (bLast : ℤ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    (scaledStateAlgebraicExponentialMajorant P state b bLast z m).majorant =
      Real.exp (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖) := rfl

/-- Pointwise comparison error based on the level-scaled algebraic
auxiliary function.  This is the error envelope used on every level-`N`
contour and interpolation node. -/
def levelAlgebraicSourceRowError {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {N : ℕ} (state : LevelState P N)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (z : ℂ)
    (linearFormBound : ℝ) (m : VDPLMultiIndex (oldRank + 1)) : ℝ :=
  (scaledStateAlgebraicExponentialMajorant P state b bLast z m).error
    linearFormBound

theorem levelAlgebraicSourceRowError_nonneg {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {N : ℕ} (state : LevelState P N)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (z : ℂ)
    {linearFormBound : ℝ} (hbound : 0 ≤ linearFormBound)
    (m : VDPLMultiIndex (oldRank + 1)) :
    0 ≤ levelAlgebraicSourceRowError
      P state b bLast z linearFormBound m := by
  unfold levelAlgebraicSourceRowError AlgebraicExponentialMajorant.error
  apply mul_nonneg
  · unfold AlgebraicExponentialMajorant.growth
    exact mul_nonneg
      (mul_nonneg
        (stateSourceMajorants P state b bLast z m).supportMajorant_nonneg
        (mul_nonneg P.coeffHeight_pos.le
          (stateSourceMajorants P state b bLast z m).deltaMajorant_nonneg))
      (scaledStateAlgebraicExponentialMajorant
        P state b bLast z m).majorant_nonneg
  · exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg
        (stateSourceMajorants P state b bLast z m).amplificationMajorant_nonneg
        hbound)

/-- Pointwise source comparison error based on the unmodified algebraic
auxiliary function. -/
def algebraicSourceRowError {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {N : ℕ} (state : LevelState P N)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (z : ℂ)
    (linearFormBound : ℝ) (m : VDPLMultiIndex (oldRank + 1)) : ℝ :=
  (stateAlgebraicExponentialMajorant P state b bLast z m).error linearFormBound

theorem algebraicSourceRowError_nonneg {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {N : ℕ} (state : LevelState P N)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (z : ℂ)
    {linearFormBound : ℝ} (hbound : 0 ≤ linearFormBound)
    (m : VDPLMultiIndex (oldRank + 1)) :
    0 ≤ algebraicSourceRowError P state b bLast z linearFormBound m := by
  unfold algebraicSourceRowError AlgebraicExponentialMajorant.error
  apply mul_nonneg
  · unfold AlgebraicExponentialMajorant.growth
    exact mul_nonneg
      (mul_nonneg
        (stateSourceMajorants P state b bLast z m).supportMajorant_nonneg
        (mul_nonneg P.coeffHeight_pos.le
          (stateSourceMajorants P state b bLast z m).deltaMajorant_nonneg))
      (stateAlgebraicExponentialMajorant P state b bLast z m).majorant_nonneg
  · exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg
        (stateSourceMajorants P state b bLast z m).amplificationMajorant_nonneg
        hbound)

/-! ## Oversized-constant absorption with algebraic growth -/

/-- The numerical three-quarter error absorption, now based on algebraic
growth.  This is the coefficient-dominance-free counterpart of
`error_smallLinearFormBound_le_exp_neg_three_quarters`. -/
theorem algebraicError_smallLinearFormBound_le_exp_neg_three_quarters
    {ι : Type*} [Fintype ι] {oldRank : ℕ} {I : Type*}
    {P : VDPLParameters ι} {coord : SourceCoordinates oldRank I}
    {support : Finset I} {p : I → ℤ}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {logAlpha : Fin oldRank → ℂ} {logAlphaLast : ℂ}
    {q N : ℕ} {z : ℂ} {m : VDPLMultiIndex (oldRank + 1)}
    {M : SourceMajorants P coord support p h b bLast logAlpha q N z m}
    (A : BakerSourceAlgebraicMajorant.AlgebraicExponentialMajorant P coord
      support p h b bLast logAlpha logAlphaLast q N z m M)
    {sourceConstant : ℝ}
    (hE : 8 ≤ sourceExponent P sourceConstant)
    (hgrowth : A.growth ≤ Real.exp (sourceExponent P sourceConstant / 16))
    (hamplification : M.amplificationMajorant ≤
      Real.exp (sourceExponent P sourceConstant / 16)) :
    A.error (smallLinearFormBound P sourceConstant) ≤
      Real.exp (-3 * sourceExponent P sourceConstant / 4) := by
  let E := sourceExponent P sourceConstant
  let B := M.amplificationMajorant
  let U := B * Real.exp (-E)
  have hE0 : 0 ≤ E := by dsimp only [E]; linarith
  have hB0 : 0 ≤ B := M.amplificationMajorant_nonneg
  have hU0 : 0 ≤ U := mul_nonneg hB0 (Real.exp_pos _).le
  have hU : U ≤ Real.exp (-15 * E / 16) := by
    calc
      U = B * Real.exp (-E) := rfl
      _ ≤ Real.exp (E / 16) * Real.exp (-E) :=
        mul_le_mul_of_nonneg_right hamplification (Real.exp_pos _).le
      _ = Real.exp (-15 * E / 16) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hU_le_one : U ≤ 1 := by
    calc
      U ≤ Real.exp (-15 * E / 16) := hU
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith)
      _ = 1 := Real.exp_zero
  have hexpU : Real.exp U ≤ Real.exp 1 := Real.exp_le_exp.mpr hU_le_one
  have hinner : Real.exp U * U ≤
      Real.exp 1 * Real.exp (-15 * E / 16) :=
    mul_le_mul hexpU hU hU0 (Real.exp_pos _).le
  change A.growth * (Real.exp U * U) ≤ Real.exp (-3 * E / 4)
  calc
    A.growth * (Real.exp U * U) ≤
        Real.exp (E / 16) *
          (Real.exp 1 * Real.exp (-15 * E / 16)) :=
      mul_le_mul hgrowth hinner
        (mul_nonneg (Real.exp_pos _).le hU0) (Real.exp_pos _).le
    _ = Real.exp (1 - 14 * E / 16) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-3 * E / 4) := by
      apply Real.exp_le_exp.mpr
      linarith

/-- Quarter-scale algebraic growth and amplification at a reference
constant imply a three-quarter comparison error at any four-times-larger
normalized source constant. -/
theorem algebraicError_le_exp_neg_three_quarters_of_oversized
    {oldRank : ℕ} [Nonempty (Fin oldRank)] {I : Type*}
    {P : VDPLParameters (Fin oldRank)}
    {coord : SourceCoordinates oldRank I} {support : Finset I} {p : I → ℤ}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {logAlpha : Fin oldRank → ℂ} {logAlphaLast : ℂ}
    {q N : ℕ} {z : ℂ} {m : VDPLMultiIndex (oldRank + 1)}
    {M : SourceMajorants P coord support p h b bLast logAlpha q N z m}
    (A : BakerSourceAlgebraicMajorant.AlgebraicExponentialMajorant P coord
      support p h b bLast logAlpha logAlphaLast q N z m M)
    {Cbase C₀ : ℝ} (hC : 4 * Cbase ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hgrowth : A.growth ≤
      Real.exp (sourceExponent P (Cbase * Real.log P.OmegaOld) / 4))
    (hamplification : M.amplificationMajorant ≤
      Real.exp (sourceExponent P (Cbase * Real.log P.OmegaOld) / 4)) :
    A.error (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) ≤
      Real.exp (-3 * sourceExponent P
        (C₀ * Real.log P.OmegaOld) / 4) := by
  apply algebraicError_smallLinearFormBound_le_exp_neg_three_quarters A hE
  · exact hgrowth.trans
      (exp_quarter_le_exp_sixteenth_of_four_mul_le P hC)
  · exact hamplification.trans
      (exp_quarter_le_exp_sixteenth_of_four_mul_le P hC)

/-- Coordinate-level comparison theorem for the corrected source state. -/
theorem norm_gSource_sub_fSource_le_algebraicSourceRowError
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1))
    {linearFormBound : ℝ} (hbound : 0 ≤ linearFormBound)
    (hsmall : ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤ linearFormBound) :
    ‖gSource state b bLast z m - fSource state b bLast z m‖ ≤
      algebraicSourceRowError P state b bLast z linearFormBound m := by
  exact norm_state_vdplG_sub_vdplF_le_algebraicError
    P state b hbLast z m hbound hsmall

/-- Coordinate-level comparison using the level-scaled algebraic base. -/
theorem norm_gSource_sub_fSource_le_levelAlgebraicSourceRowError
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1))
    {linearFormBound : ℝ} (hbound : 0 ≤ linearFormBound)
    (hsmall : ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤ linearFormBound) :
    ‖gSource state b bLast z m - fSource state b bLast z m‖ ≤
      levelAlgebraicSourceRowError
        P state b bLast z linearFormBound m := by
  exact (scaledStateAlgebraicExponentialMajorant
    P state b bLast z m).norm_vdplG_sub_vdplF_le_error
      hbLast hbound hsmall

/-- Coordinate-level direct growth estimate for `f`. -/
theorem norm_fSource_le_stateAlgebraicAnalyticGrowth
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (z : ℂ) (m : VDPLMultiIndex (oldRank + 1))
    {linearFormBound : ℝ} (hbound : 0 ≤ linearFormBound)
    (hsmall : ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤ linearFormBound) :
    ‖fSource state b bLast z m‖ ≤
      AlgebraicExponentialMajorant.analyticGrowth
        (stateAlgebraicExponentialMajorant P state b bLast z m)
        linearFormBound := by
  exact AlgebraicExponentialMajorant.norm_vdplF_le_analyticGrowth
    (stateAlgebraicExponentialMajorant P state b bLast z m)
    hbLast hbound hsmall

/-- Parameter-rank direct growth estimate for `f`. -/
theorem norm_f_le_stateAlgebraicAnalyticGrowth
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0) (z : ℂ) (m : VDPLMultiIndex P.rank)
    {linearFormBound : ℝ} (hbound : 0 ≤ linearFormBound)
    (hsmall : ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤ linearFormBound) :
    ‖f state b bLast z m‖ ≤
      AlgebraicExponentialMajorant.analyticGrowth
        (stateAlgebraicExponentialMajorant P state b bLast z
          (toSourceMultiIndex P m)) linearFormBound := by
  exact norm_fSource_le_stateAlgebraicAnalyticGrowth P state b hbLast z
    (toSourceMultiIndex P m) hbound hsmall

/-- Equation (8) with the source-faithful algebraic comparison error. -/
theorem norm_normalizedIteratedDeriv_f_le_algebraicSourceError_of_integralSeed
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : IntegralSeedAtLevel P (g state b bLast) N)
    (C₀ : ℝ)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    {l j : ℕ} (hl : 1 ≤ l) (hlR : l ≤ P.R N)
    (m : VDPLMultiIndex P.rank)
    (hmj : VDPLMultiIndex.weight m + j ≤ P.Slevel N) :
    ‖iteratedDeriv j (fun w ↦ f state b bLast w m) (l : ℂ) /
        (j.factorial : ℂ)‖ ≤
      jetErrorIterate P N bLast j
          (algebraicSourceRowError P state b bLast (l : ℂ)
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
          (toSourceMultiIndex P m) /
        ‖(j.factorial : ℂ)‖ := by
  apply norm_normalizedIteratedDeriv_f_le_jetErrorIterate_of_vanishesOn
    state b hbLast
    (by simpa only [IntegralSeedAtLevel] using hseed)
    (algebraicSourceRowError P state b bLast (l : ℂ)
      (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
  · intro m'
    exact algebraicSourceRowError_nonneg P state b bLast (l : ℂ)
      (by unfold smallLinearFormBound; positivity) m'
  · exact hl
  · exact hlR
  · intro m' _hm'
    have hform := norm_logForm_le_smallLinearFormBound_of_normalized
      P C₀ b bLast hsmall
    have hcomparison :=
      norm_gSource_sub_fSource_le_algebraicSourceRowError P state b hbLast
        (l : ℂ) m' (by unfold smallLinearFormBound; positivity) hform
    simpa only [norm_sub_rev] using hcomparison
  · exact hmj

/-- Equation (8) with the level-scaled algebraic comparison error. -/
theorem
    norm_normalizedIteratedDeriv_f_le_levelAlgebraicSourceError_of_integralSeed
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : IntegralSeedAtLevel P (g state b bLast) N)
    (C₀ : ℝ)
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    {l j : ℕ} (hl : 1 ≤ l) (hlR : l ≤ P.R N)
    (m : VDPLMultiIndex P.rank)
    (hmj : VDPLMultiIndex.weight m + j ≤ P.Slevel N) :
    ‖iteratedDeriv j (fun w ↦ f state b bLast w m) (l : ℂ) /
        (j.factorial : ℂ)‖ ≤
      jetErrorIterate P N bLast j
          (levelAlgebraicSourceRowError P state b bLast (l : ℂ)
            (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
          (toSourceMultiIndex P m) /
        ‖(j.factorial : ℂ)‖ := by
  apply norm_normalizedIteratedDeriv_f_le_jetErrorIterate_of_vanishesOn
    state b hbLast
    (by simpa only [IntegralSeedAtLevel] using hseed)
    (levelAlgebraicSourceRowError P state b bLast (l : ℂ)
      (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
  · intro m'
    exact levelAlgebraicSourceRowError_nonneg P state b bLast (l : ℂ)
      (by unfold smallLinearFormBound; positivity) m'
  · exact hl
  · exact hlR
  · intro m' _hm'
    have hform := norm_logForm_le_smallLinearFormBound_of_normalized
      P C₀ b bLast hsmall
    have hcomparison :=
      norm_gSource_sub_fSource_le_levelAlgebraicSourceRowError
        P state b hbLast (l : ℂ) m'
          (by unfold smallLinearFormBound; positivity) hform
    simpa only [norm_sub_rev] using hcomparison
  · exact hmj

/-- Final equation-(7)--(8) estimate based on algebraic growth.  The two
remaining hypotheses are coefficient-independent source growth and
amplification estimates; no ordering of the coefficients `b r` is present. -/
theorem
    norm_normalizedIteratedDeriv_f_le_exp_neg_two_thirds_of_algebraicOversized
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : IntegralSeedAtLevel P (g state b bLast) N)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hjet : jetAbsorptionConstant P ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (l j : ℕ) (hl : 1 ≤ l) (hlR : l ≤ P.R N)
    (hgrowth : ∀ m', VDPLMultiIndex.weight m' ≤ P.Slevel N →
      (stateAlgebraicExponentialMajorant P state b bLast (l : ℂ) m').growth ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (hamplification : ∀ m', VDPLMultiIndex.weight m' ≤ P.Slevel N →
      (stateSourceMajorants P state b bLast (l : ℂ) m').amplificationMajorant ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (m : VDPLMultiIndex P.rank)
    (hmj : VDPLMultiIndex.weight m + j ≤ P.Slevel N) :
    ‖iteratedDeriv j (fun w ↦ f state b bLast w m) (l : ℂ) /
        (j.factorial : ℂ)‖ ≤
      Real.exp
        (-2 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 3) := by
  have hbase :=
    norm_normalizedIteratedDeriv_f_le_algebraicSourceError_of_integralSeed
      state b hbLast hseed C₀ hsmall hl hlR m hmj
  refine hbase.trans ?_
  apply jetErrorIterate_div_factorial_le_exp_neg_two_thirds
    P N bLast hbLast j
    (algebraicSourceRowError P state b bLast (l : ℂ)
      (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)))
  · intro m'
    exact algebraicSourceRowError_nonneg P state b bLast (l : ℂ)
      (by unfold smallLinearFormBound; positivity) m'
  · exact hjet
  · intro m' hm'
    exact algebraicError_le_exp_neg_three_quarters_of_oversized
      (stateAlgebraicExponentialMajorant P state b bLast (l : ℂ) m')
      hstruct hE (hgrowth m' hm') (hamplification m' hm')
  · simpa only [weight_toSourceMultiIndex] using hmj

/-- Final equation-(7)--(8) estimate with the level-scaled algebraic
comparison error.  This is the form used by the Lemma-4 induction. -/
theorem
    norm_normalizedIteratedDeriv_f_le_exp_neg_two_thirds_of_levelAlgebraicOversized
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    {P : VDPLParameters (Fin oldRank)} {N : ℕ}
    (state : LevelState P N) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hbLast : bLast ≠ 0)
    (hseed : IntegralSeedAtLevel P (g state b bLast) N)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hjet : jetAbsorptionConstant P ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hsmall :
      |RationalPrimeBaker.indexedRationalLogForm
          P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ))))
    (l j : ℕ) (hl : 1 ≤ l) (hlR : l ≤ P.R N)
    (hgrowth : ∀ m', VDPLMultiIndex.weight m' ≤ P.Slevel N →
      (scaledStateAlgebraicExponentialMajorant
        P state b bLast (l : ℂ) m').growth ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (hamplification : ∀ m', VDPLMultiIndex.weight m' ≤ P.Slevel N →
      (stateSourceMajorants P state b bLast (l : ℂ) m').amplificationMajorant ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (m : VDPLMultiIndex P.rank)
    (hmj : VDPLMultiIndex.weight m + j ≤ P.Slevel N) :
    ‖iteratedDeriv j (fun w ↦ f state b bLast w m) (l : ℂ) /
        (j.factorial : ℂ)‖ ≤
      Real.exp
        (-2 * sourceExponent P (C₀ * Real.log P.OmegaOld) / 3) := by
  have hbase :=
    norm_normalizedIteratedDeriv_f_le_levelAlgebraicSourceError_of_integralSeed
      state b hbLast hseed C₀ hsmall hl hlR m hmj
  refine hbase.trans ?_
  apply jetErrorIterate_div_factorial_le_exp_neg_two_thirds
    P N bLast hbLast j
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

#print axioms AlgebraicExponentialMajorant.norm_vdplF_le_analyticGrowth
#print axioms norm_gSource_sub_fSource_le_algebraicSourceRowError
#print axioms norm_gSource_sub_fSource_le_levelAlgebraicSourceRowError
#print axioms norm_normalizedIteratedDeriv_f_le_algebraicSourceError_of_integralSeed
#print axioms norm_normalizedIteratedDeriv_f_le_exp_neg_two_thirds_of_algebraicOversized
#print axioms
  norm_normalizedIteratedDeriv_f_le_levelAlgebraicSourceError_of_integralSeed
#print axioms
  norm_normalizedIteratedDeriv_f_le_exp_neg_two_thirds_of_levelAlgebraicOversized

end Erdos240.BakerSourceAlgebraicMomentBounds
