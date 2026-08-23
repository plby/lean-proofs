/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAlgebraicMomentBounds
import ErdosProblems.Erdos240.BakerSourceAlgebraicExponentAbsorption

/-!
# Level-scaled algebraic source majorants

The algebraic rate at induction level `J` uses exponent sides divided by
`q ^ J`.  Retaining this factor is essential on the source contours, whose
radii grow like `q ^ J`.  This file refines the state specialization of the
canonical algebraic majorant to

`exp (q⁻ᴶ * sourceAlgebraicRateBound * ‖z‖)`.

It is independent of all logarithmic-form coefficients and therefore needs
no coefficient-dominance hypothesis.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceAlgebraicLevelMajorant

open Finset
open Erdos240
open BakerLemma3
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerSourceAlgebraicMajorant
open BakerSourceAlgebraicMajorant.AlgebraicExponentialMajorant
open BakerSourceAlgebraicMomentBounds
open BakerSourceState

/-- An old exponential coordinate at level `J` retains its exact
`q ^ (-J)` scale. -/
theorem state_oldExponent_cast_le_qInvPow {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (lambda : LevelIndex P J) (r : Fin oldRank) :
    ((coordinatesForState state).oldExponent lambda r : ℝ) ≤
      P.qInvPow J * (P.LiZero r : ℝ) := by
  calc
    ((coordinatesForState state).oldExponent lambda r : ℝ) ≤
        ((levelBoxShape P J).oldMax r : ℕ) := by
      exact_mod_cast Nat.le_of_lt_succ (lambda.oldExponentFin r).isLt
    _ = (scaledExponentMax P J (P.LiZero r) : ℕ) := rfl
    _ ≤ P.qInvPow J * (P.LiZero r : ℝ) :=
      scaledExponentMax_cast_le P J (P.LiZero r)

/-- The last exponential coordinate has the same level scale. -/
theorem state_lastExponent_cast_le_qInvPow {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (lambda : LevelIndex P J) :
    ((coordinatesForState state).lastExponent lambda : ℝ) ≤
      P.qInvPow J * (P.LlastZero : ℝ) := by
  calc
    ((coordinatesForState state).lastExponent lambda : ℝ) ≤
        ((levelBoxShape P J).lastMax : ℕ) := by
      exact_mod_cast Nat.le_of_lt_succ lambda.lastExponentFin.isLt
    _ = (scaledExponentMax P J P.LlastZero : ℕ) := rfl
    _ ≤ P.qInvPow J * (P.LlastZero : ℝ) :=
      scaledExponentMax_cast_le P J P.LlastZero

/-- Level-scaled algebraic-rate bound.  This is the rate estimate used on
all integral, rational, and coprime contours. -/
theorem norm_state_algebraicRate_le_qInvPow {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (lambda : LevelIndex P J) :
    ‖algebraicRate (coordinatesForState state) (oldLog P) (lastLog P) lambda‖ ≤
      P.qInvPow J * sourceAlgebraicRateBound P := by
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
          (P.qInvPow J * (P.LiZero r : ℝ)) * ‖oldLog P r‖) +
          (P.qInvPow J * (P.LlastZero : ℝ)) * ‖lastLog P‖ := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro r _hr
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right
          (state_oldExponent_cast_le_qInvPow P state lambda r)
          (norm_nonneg _)
      · rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right
          (state_lastExponent_cast_le_qInvPow P state lambda)
          (norm_nonneg _)
    _ = P.qInvPow J *
          ((∑ r, (P.LiZero r : ℝ) * ‖oldLog P r‖) +
            (P.LlastZero : ℝ) * ‖lastLog P‖) := by
      rw [mul_add, Finset.mul_sum]
      ring

/-- Canonical algebraic exponential majorant retaining the level factor
`q ^ (-J)`.  This is the shared scaled state majorant used by the row-error
and moment-cancellation consumers. -/
abbrev levelAlgebraicExponentialMajorant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    AlgebraicExponentialMajorant P (coordinatesForState state) state.support
      state.coeff P.h b bLast (oldLog P) (lastLog P) P.q J z m
      (stateSourceMajorants P state b bLast z m) :=
  scaledStateAlgebraicExponentialMajorant P state b bLast z m

@[simp] theorem levelAlgebraicExponentialMajorant_majorant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    (levelAlgebraicExponentialMajorant P state b bLast z m).majorant =
      Real.exp (P.qInvPow J * sourceAlgebraicRateBound P * ‖z‖) := rfl

/-- Level-scaled growth estimate for the unmodified auxiliary function. -/
theorem norm_state_vdplG_le_levelAlgebraicGrowth {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    ‖vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
        (oldLog P) (lastLog P) P.q J z m‖ ≤
      (levelAlgebraicExponentialMajorant P state b bLast z m).growth :=
  (levelAlgebraicExponentialMajorant P state b bLast z m).norm_vdplG_le_growth

/-- Level-scaled direct growth estimate for the modified auxiliary function,
obtained from the exact source factorization. -/
theorem norm_fSource_le_levelAlgebraicAnalyticGrowth {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) {bLast : ℤ} (hbLast : bLast ≠ 0)
    (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) {linearFormBound : ℝ}
    (hbound : 0 ≤ linearFormBound)
    (hsmall : ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤ linearFormBound) :
    ‖fSource state b bLast z m‖ ≤
      BakerSourceAlgebraicMomentBounds.AlgebraicExponentialMajorant.analyticGrowth
        (levelAlgebraicExponentialMajorant P state b bLast z m)
        linearFormBound := by
  exact BakerSourceAlgebraicMomentBounds.AlgebraicExponentialMajorant.norm_vdplF_le_analyticGrowth
    (levelAlgebraicExponentialMajorant P state b bLast z m)
    hbLast hbound hsmall

/-- The corresponding rank-indexed consumer used by Lemmas 4--6. -/
theorem norm_f_le_levelAlgebraicAnalyticGrowth {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) {bLast : ℤ} (hbLast : bLast ≠ 0)
    (z : ℂ) (m : VDPLMultiIndex P.rank) {linearFormBound : ℝ}
    (hbound : 0 ≤ linearFormBound)
    (hsmall : ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤ linearFormBound) :
    ‖f state b bLast z m‖ ≤
      BakerSourceAlgebraicMomentBounds.AlgebraicExponentialMajorant.analyticGrowth
        (levelAlgebraicExponentialMajorant P state b bLast z
          (toSourceMultiIndex P m)) linearFormBound := by
  exact norm_fSource_le_levelAlgebraicAnalyticGrowth
    P state b hbLast z (toSourceMultiIndex P m) hbound hsmall

#print axioms state_oldExponent_cast_le_qInvPow
#print axioms norm_state_algebraicRate_le_qInvPow
#print axioms norm_state_vdplG_le_levelAlgebraicGrowth
#print axioms norm_f_le_levelAlgebraicAnalyticGrowth

end Erdos240.BakerSourceAlgebraicLevelMajorant
