/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAlgebraicLevelMajorant

/-!
# Uniform source bounds for the algebraic majorant

The ordinary old-coordinate Delta factors must retain both pieces of the
source's factorial-sensitive estimate:

`|Delta(x;m)| <= (2 B)^m * 2^L` when `|x| <= B L`.

Using the coarser bound `(B L + 1)^m` introduces a spurious logarithm of
the varying height.  This file proves the sharp estimate at every induction
level and packages it as a closed bound for the exact finite-sum Delta
majorant.  Both the exponent sides and the algebraic exponential retain
their exact `q ^ (-J)` scaling.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceAlgebraicUniformBounds

open Finset
open Erdos240
open BakerLemma2Concrete
open BakerLemma3
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerSourceAlgebraicMajorant
open BakerSourceAlgebraicMajorant.AlgebraicExponentialMajorant
open BakerSourceAlgebraicMomentBounds
open BakerSourceAlgebraicLevelMajorant
open BakerSourceMajorantClosedForm
open BakerSourceState

/-- The sum of the old-coordinate side lengths which occurs in the sharp
binary-binomial Delta estimate at level `J`. -/
def levelOldDeltaSideSum {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) : ℕ :=
  ∑ r : Fin oldRank,
    ((levelBoxShape P J).oldMax r + (levelBoxShape P J).lastMax)

/-- The exact `q ^ (-J)` bound on the binary-binomial side exponent. -/
theorem levelOldDeltaSideSum_cast_le {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) :
    (levelOldDeltaSideSum P J : ℝ) ≤
      P.qInvPow J *
        ((1 / 4 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
          Real.log P.OmegaOld) := by
  have hterm (r : Fin oldRank) :
      (((levelBoxShape P J).oldMax r +
          (levelBoxShape P J).lastMax : ℕ) : ℝ) ≤
        P.qInvPow J * ((P.LiZero r + P.LlastZero : ℕ) : ℝ) := by
    push_cast
    calc
      ((levelBoxShape P J).oldMax r : ℝ) +
          ((levelBoxShape P J).lastMax : ℝ) ≤
        P.qInvPow J * (P.LiZero r : ℝ) +
          P.qInvPow J * (P.LlastZero : ℝ) :=
        add_le_add
          (scaledExponentMax_cast_le P J (P.LiZero r))
          (scaledExponentMax_cast_le P J P.LlastZero)
      _ = P.qInvPow J *
          (((P.LiZero r : ℝ) + P.LlastZero)) := by ring
  calc
    (levelOldDeltaSideSum P J : ℝ) =
        ∑ r : Fin oldRank,
          (((levelBoxShape P J).oldMax r +
            (levelBoxShape P J).lastMax : ℕ) : ℝ) := by
      simp only [levelOldDeltaSideSum, Nat.cast_sum]
    _ ≤ ∑ r : Fin oldRank,
          P.qInvPow J * ((P.LiZero r + P.LlastZero : ℕ) : ℝ) :=
      Finset.sum_le_sum fun r _hr ↦ hterm r
    _ = P.qInvPow J *
          ((∑ r : Fin oldRank, (P.LiZero r + P.LlastZero) : ℕ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
    _ ≤ P.qInvPow J *
        ((1 / 4 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
          Real.log P.OmegaOld) :=
      mul_le_mul_of_nonneg_left (initial_oldDeltaSideSum_le P)
        (P.qInvPow_pos J).le

/-- A level-scaled signed old-coordinate argument. -/
theorem state_old_delta_argument_natAbs_le_levelSides {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLast : bLast.natAbs ≤ P.Bsrc)
    (lambda : LevelIndex P J) (r : Fin oldRank) :
    (bLast * (coordinatesForState state).oldExponent lambda r -
        b r * (coordinatesForState state).lastExponent lambda).natAbs ≤
      P.Bsrc * ((levelBoxShape P J).oldMax r +
        (levelBoxShape P J).lastMax) := by
  have hold : (coordinatesForState state).oldExponent lambda r ≤
      (levelBoxShape P J).oldMax r :=
    Nat.le_of_lt_succ (lambda.oldExponentFin r).isLt
  have hlast : (coordinatesForState state).lastExponent lambda ≤
      (levelBoxShape P J).lastMax :=
    Nat.le_of_lt_succ lambda.lastExponentFin.isLt
  calc
    (bLast * (coordinatesForState state).oldExponent lambda r -
          b r * (coordinatesForState state).lastExponent lambda).natAbs ≤
        (bLast * (coordinatesForState state).oldExponent lambda r).natAbs +
          (b r * (coordinatesForState state).lastExponent lambda).natAbs :=
      Int.natAbs_sub_le _ _
    _ = bLast.natAbs *
          (coordinatesForState state).oldExponent lambda r +
        (b r).natAbs *
          (coordinatesForState state).lastExponent lambda := by
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
    _ ≤ P.Bsrc * (levelBoxShape P J).oldMax r +
        P.Bsrc * (levelBoxShape P J).lastMax :=
      Nat.add_le_add (Nat.mul_le_mul hbLast hold) (Nat.mul_le_mul (hb r) hlast)
    _ = P.Bsrc * ((levelBoxShape P J).oldMax r +
        (levelBoxShape P J).lastMax) := by rw [Nat.mul_add]

/-- Factorial-sensitive bound for one ordinary old-coordinate Delta factor
in an arbitrary source state. -/
theorem norm_state_simpleDeltaEval_le_sharp {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLast : bLast.natAbs ≤ P.Bsrc)
    (lambda : LevelIndex P J) (m : VDPLMultiIndex (oldRank + 1))
    (r : Fin oldRank) :
    ‖simpleDeltaEval (m r.succ)
        ((bLast : ℂ) * (coordinatesForState state).oldExponent lambda r -
          (b r : ℂ) * (coordinatesForState state).lastExponent lambda)‖ ≤
      ((2 * P.Bsrc : ℕ) : ℝ) ^ (m r.succ) *
        (2 : ℝ) ^ ((levelBoxShape P J).oldMax r +
          (levelBoxShape P J).lastMax) := by
  let a : ℤ := bLast * (coordinatesForState state).oldExponent lambda r -
    b r * (coordinatesForState state).lastExponent lambda
  have harg :
      (bLast : ℂ) * (coordinatesForState state).oldExponent lambda r -
          (b r : ℂ) * (coordinatesForState state).lastExponent lambda =
        (a : ℂ) := by
    dsimp only [a]
    push_cast
    rfl
  have hB : 1 ≤ P.Bsrc := by
    have hBreal : (1 : ℝ) ≤ P.Bsrc :=
      (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans P.Bsrc_lower
    exact_mod_cast hBreal
  have hrat := abs_delta_eval_int_le_pow_mul_budgetSide
    (m r.succ) P.Bsrc
    ((levelBoxShape P J).oldMax r + (levelBoxShape P J).lastMax) a hB
    (state_old_delta_argument_natAbs_le_levelSides
      P state b bLast hb hbLast lambda r)
  rw [harg]
  unfold simpleDeltaEval
  rw [show (a : ℂ) = algebraMap ℚ ℂ (a : ℚ) by norm_num,
    Polynomial.eval₂_at_apply]
  change ‖((((Erdos240Delta.delta (m r.succ)).eval (a : ℚ)) : ℚ) : ℂ)‖ ≤ _
  rw [Complex.norm_ratCast]
  exact_mod_cast hrat

/-- The product of all ordinary old-coordinate Delta factors keeps the
source's sharp `(2B)^weight * 2^(scaled side sum)` form. -/
theorem norm_state_oldDeltaProduct_le_sharp {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLast : bLast.natAbs ≤ P.Bsrc)
    (lambda : LevelIndex P J) (m : VDPLMultiIndex (oldRank + 1))
    {S : ℕ} (hm : VDPLMultiIndex.weight m ≤ S) :
    ‖∏ r : Fin oldRank, simpleDeltaEval (m r.succ)
        ((bLast : ℂ) * (coordinatesForState state).oldExponent lambda r -
          (b r : ℂ) * (coordinatesForState state).lastExponent lambda)‖ ≤
      ((2 * P.Bsrc : ℕ) : ℝ) ^ S *
        (2 : ℝ) ^ levelOldDeltaSideSum P J := by
  have hsum : (∑ r : Fin oldRank, m r.succ) ≤ S := by
    have hdecomp :
        VDPLMultiIndex.weight m = m 0 + ∑ r : Fin oldRank, m r.succ := by
      simp only [VDPLMultiIndex.weight, Fin.sum_univ_succ]
    omega
  have hbase : (1 : ℝ) ≤ ((2 * P.Bsrc : ℕ) : ℝ) := by
    have hB : 1 ≤ P.Bsrc := by
      have hBreal : (1 : ℝ) ≤ P.Bsrc :=
        (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans P.Bsrc_lower
      exact_mod_cast hBreal
    exact_mod_cast (show 1 ≤ 2 * P.Bsrc by omega)
  calc
    ‖∏ r : Fin oldRank, simpleDeltaEval (m r.succ)
        ((bLast : ℂ) * (coordinatesForState state).oldExponent lambda r -
          (b r : ℂ) * (coordinatesForState state).lastExponent lambda)‖ =
      ∏ r : Fin oldRank, ‖simpleDeltaEval (m r.succ)
        ((bLast : ℂ) * (coordinatesForState state).oldExponent lambda r -
          (b r : ℂ) * (coordinatesForState state).lastExponent lambda)‖ := by
        rw [norm_prod]
    _ ≤ ∏ r : Fin oldRank,
        (((2 * P.Bsrc : ℕ) : ℝ) ^ (m r.succ) *
          (2 : ℝ) ^ ((levelBoxShape P J).oldMax r +
            (levelBoxShape P J).lastMax)) :=
      Finset.prod_le_prod
        (fun r _hr ↦ norm_nonneg (simpleDeltaEval (m r.succ)
          ((bLast : ℂ) * (coordinatesForState state).oldExponent lambda r -
            (b r : ℂ) * (coordinatesForState state).lastExponent lambda)))
        (fun r _hr ↦ norm_state_simpleDeltaEval_le_sharp
          P state b bLast hb hbLast lambda m r)
    _ = ((2 * P.Bsrc : ℕ) : ℝ) ^ (∑ r : Fin oldRank, m r.succ) *
        (2 : ℝ) ^ levelOldDeltaSideSum P J := by
      unfold levelOldDeltaSideSum
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        Finset.prod_pow_eq_pow_sum]
    _ ≤ ((2 * P.Bsrc : ℕ) : ℝ) ^ S *
        (2 : ℝ) ^ levelOldDeltaSideSum P J :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase hsum) (by positivity)

/-- Factorial-sensitive closed envelope for every auxiliary Delta factor. -/
def sourceSharpDeltaFactorMajorant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (z : ℂ) (S : ℕ) : ℝ :=
  sourceHeadDeltaMajorant P J z *
    (((2 * P.Bsrc : ℕ) : ℝ) ^ S *
      (2 : ℝ) ^ levelOldDeltaSideSum P J)

theorem sourceSharpDeltaFactorMajorant_nonneg {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (z : ℂ) (S : ℕ) :
    0 ≤ sourceSharpDeltaFactorMajorant P J z S := by
  unfold sourceSharpDeltaFactorMajorant sourceHeadDeltaMajorant
  positivity

theorem norm_state_auxiliaryFactor_le_sourceSharpDeltaFactorMajorant
    {oldRank : ℕ} (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLast : bLast.natAbs ≤ P.Bsrc)
    (lambda : LevelIndex P J) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) {S : ℕ}
    (hm : VDPLMultiIndex.weight m ≤ S) :
    ‖auxiliaryFactor (coordinatesForState state) P.h b bLast lambda
        (scaledArgument P.q J z) m‖ ≤
      sourceSharpDeltaFactorMajorant P J z S := by
  unfold auxiliaryFactor sourceSharpDeltaFactorMajorant
  rw [norm_mul]
  have holdNonneg :
      0 ≤ ‖∏ r : Fin oldRank,
        simpleDeltaEval (m r.succ)
          ((bLast : ℂ) * (coordinatesForState state).oldExponent lambda r -
            (b r : ℂ) * (coordinatesForState state).lastExponent lambda)‖ :=
    norm_nonneg _
  have hheadNonneg :
      0 ≤ sourceHeadDeltaMajorant P J z := by
    unfold sourceHeadDeltaMajorant
    exact pow_nonneg (by norm_num) _
  exact mul_le_mul
    (norm_state_poweredDeltaHasseEval_le_sourceHeadDeltaMajorant
      P state lambda z m)
    (norm_state_oldDeltaProduct_le_sharp
      P state b bLast hb hbLast lambda m hm)
    holdNonneg
    hheadNonneg

/-- The exact finite-sum Delta majorant is bounded by the source-faithful
factorial-sensitive closed form. -/
theorem deltaMajorant_le_sharpClosedForm {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLast : bLast.natAbs ≤ P.Bsrc) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) {S : ℕ}
    (hm : VDPLMultiIndex.weight m ≤ S) :
    (stateSourceMajorants P state b bLast z m).deltaMajorant ≤
      (initialSupportBound P : ℝ) *
        sourceSharpDeltaFactorMajorant P J z S := by
  unfold stateSourceMajorants exactSourceMajorants
  dsimp only
  calc
    ∑ lambda ∈ state.support,
        ‖auxiliaryFactor (coordinatesForState state) P.h b bLast lambda
          (scaledArgument P.q J z) m‖ ≤
      ∑ _lambda ∈ state.support,
        sourceSharpDeltaFactorMajorant P J z S := by
      apply Finset.sum_le_sum
      intro lambda _hlambda
      exact norm_state_auxiliaryFactor_le_sourceSharpDeltaFactorMajorant
        P state b bLast hb hbLast lambda z m hm
    _ = (state.support.card : ℝ) *
        sourceSharpDeltaFactorMajorant P J z S := by simp
    _ ≤ (initialSupportBound P : ℝ) *
        sourceSharpDeltaFactorMajorant P J z S :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast state_support_card_le_initialSupportBound P state)
        (sourceSharpDeltaFactorMajorant_nonneg P J z S)

/-! ## Closed source-faithful growth envelopes -/

/-- The closed algebraic-growth envelope obtained by combining the exact
support, coefficient, sharp Delta, and level-scaled algebraic-rate factors. -/
def sourceSharpAlgebraicGrowthMajorant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (z : ℂ) (S : ℕ) : ℝ :=
  (initialSupportBound P : ℝ) *
    (P.coeffHeight *
      ((initialSupportBound P : ℝ) *
        sourceSharpDeltaFactorMajorant P J z S)) *
    Real.exp (P.qInvPow J * sourceAlgebraicRateBound P * ‖z‖)

theorem sourceSharpAlgebraicGrowthMajorant_nonneg {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (z : ℂ) (S : ℕ) :
    0 ≤ sourceSharpAlgebraicGrowthMajorant P J z S := by
  unfold sourceSharpAlgebraicGrowthMajorant
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg P.coeffHeight_pos.le
        (mul_nonneg (Nat.cast_nonneg _)
          (sourceSharpDeltaFactorMajorant_nonneg P J z S))))
    (Real.exp_pos _).le

/-- The actual algebraic growth majorant is bounded by the completely
closed sharp envelope.  In particular, no internal `deltaMajorant` remains. -/
theorem levelAlgebraicGrowth_le_sharpClosedForm {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLast : bLast.natAbs ≤ P.Bsrc) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) {S : ℕ}
    (hm : VDPLMultiIndex.weight m ≤ S) :
    (levelAlgebraicExponentialMajorant P state b bLast z m).growth ≤
      sourceSharpAlgebraicGrowthMajorant P J z S := by
  have hsupport :
      (stateSourceMajorants P state b bLast z m).supportMajorant ≤
        (initialSupportBound P : ℝ) := by
    unfold stateSourceMajorants exactSourceMajorants
    dsimp only
    exact_mod_cast state_support_card_le_initialSupportBound P state
  have hdelta := deltaMajorant_le_sharpClosedForm
    P state b bLast hb hbLast z m hm
  have hcoeffDelta :
      P.coeffHeight *
          (stateSourceMajorants P state b bLast z m).deltaMajorant ≤
        P.coeffHeight *
          ((initialSupportBound P : ℝ) *
            sourceSharpDeltaFactorMajorant P J z S) :=
    mul_le_mul_of_nonneg_left hdelta P.coeffHeight_pos.le
  have hleft :
      (stateSourceMajorants P state b bLast z m).supportMajorant *
          (P.coeffHeight *
            (stateSourceMajorants P state b bLast z m).deltaMajorant) ≤
        (initialSupportBound P : ℝ) *
          (P.coeffHeight *
            ((initialSupportBound P : ℝ) *
              sourceSharpDeltaFactorMajorant P J z S)) := by
    exact mul_le_mul hsupport hcoeffDelta
      (mul_nonneg P.coeffHeight_pos.le
        (stateSourceMajorants P state b bLast z m).deltaMajorant_nonneg)
      (by positivity)
  unfold AlgebraicExponentialMajorant.growth
  rw [levelAlgebraicExponentialMajorant_majorant]
  unfold sourceSharpAlgebraicGrowthMajorant
  exact mul_le_mul_of_nonneg_right hleft (Real.exp_pos _).le

/-- The same sharp envelope bounds the unmodified algebraic function. -/
theorem norm_state_vdplG_le_sharpClosedForm {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLast : bLast.natAbs ≤ P.Bsrc) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) {S : ℕ}
    (hm : VDPLMultiIndex.weight m ≤ S) :
    ‖vdplG (coordinatesForState state) state.support state.coeff P.h b bLast
        (oldLog P) (lastLog P) P.q J z m‖ ≤
      sourceSharpAlgebraicGrowthMajorant P J z S :=
  (norm_state_vdplG_le_levelAlgebraicGrowth P state b bLast z m).trans
    (levelAlgebraicGrowth_le_sharpClosedForm
      P state b bLast hb hbLast z m hm)

/-- The direct analytic envelope for `f`, with both the Delta sum and the
amplification sum replaced by source-faithful closed forms. -/
def sourceSharpAnalyticGrowthMajorant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) (z : ℂ) (S : ℕ)
    (linearFormBound : ℝ) : ℝ :=
  sourceSharpAlgebraicGrowthMajorant P J z S *
    Real.exp (((initialSupportBound P : ℝ) *
      (P.qInvPow J * P.LlastZero) * ‖z‖) * linearFormBound)

/-- Direct source-faithful bound for the modified auxiliary function.  Its
only coefficient condition beyond source-box membership is `bLast ≠ 0`. -/
theorem norm_fSource_le_sharpClosedForm {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) {S : ℕ}
    (hm : VDPLMultiIndex.weight m ≤ S) {linearFormBound : ℝ}
    (hbound : 0 ≤ linearFormBound)
    (hsmall : ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤ linearFormBound) :
    ‖fSource state b bLast z m‖ ≤
      sourceSharpAnalyticGrowthMajorant P J z S linearFormBound := by
  refine (norm_fSource_le_levelAlgebraicAnalyticGrowth
    P state b hbLast z m hbound hsmall).trans ?_
  unfold sourceSharpAnalyticGrowthMajorant
  unfold BakerSourceAlgebraicMomentBounds.AlgebraicExponentialMajorant.analyticGrowth
  exact mul_le_mul
    (levelAlgebraicGrowth_le_sharpClosedForm
      P state b bLast hb hbLastBound z m hm)
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (amplificationMajorant_le_scaledClosedForm
        P state b hbLast z m) hbound))
    (Real.exp_pos _).le
    (sourceSharpAlgebraicGrowthMajorant_nonneg P J z S)

/-- Rank-indexed direct consumer of the sharp source-faithful bound. -/
theorem norm_f_le_sharpClosedForm {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    (z : ℂ) (m : VDPLMultiIndex P.rank) {S : ℕ}
    (hm : VDPLMultiIndex.weight m ≤ S) {linearFormBound : ℝ}
    (hbound : 0 ≤ linearFormBound)
    (hsmall : ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤ linearFormBound) :
    ‖f state b bLast z m‖ ≤
      sourceSharpAnalyticGrowthMajorant P J z S linearFormBound := by
  exact norm_fSource_le_sharpClosedForm P state b hb hbLastBound hbLast z
    (toSourceMultiIndex P m) (by
      simpa only [weight_toSourceMultiIndex] using hm) hbound hsmall

/-- Three-quarter comparison-error absorption from the sharp closed growth
and scaled amplification bounds.  This is the pointwise input used at both
old interpolation nodes and new Liouville targets. -/
theorem levelAlgebraicSourceRowError_le_exp_neg_three_quarters_of_closedForm
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) {bLast : ℤ}
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    (z : ℂ) (m : VDPLMultiIndex (oldRank + 1)) {S : ℕ}
    (hm : VDPLMultiIndex.weight m ≤ S)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hgrowth : sourceSharpAlgebraicGrowthMajorant P J z S ≤
      Real.exp
        (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (hamplification :
      (initialSupportBound P : ℝ) *
          (P.qInvPow J * P.LlastZero) * ‖z‖ ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4)) :
    levelAlgebraicSourceRowError P state b bLast z
        (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) m ≤
      Real.exp (-3 * sourceExponent P
        (C₀ * Real.log P.OmegaOld) / 4) := by
  apply algebraicError_le_exp_neg_three_quarters_of_oversized
    (levelAlgebraicExponentialMajorant P state b bLast z m)
    hstruct hE
  · exact (levelAlgebraicGrowth_le_sharpClosedForm
      P state b bLast hb hbLastBound z m hm).trans hgrowth
  · exact (amplificationMajorant_le_scaledClosedForm
      P state b hbLast z m).trans hamplification

#print axioms levelOldDeltaSideSum_cast_le
#print axioms norm_state_simpleDeltaEval_le_sharp
#print axioms norm_state_oldDeltaProduct_le_sharp
#print axioms deltaMajorant_le_sharpClosedForm
#print axioms levelAlgebraicGrowth_le_sharpClosedForm
#print axioms norm_state_vdplG_le_sharpClosedForm
#print axioms norm_fSource_le_sharpClosedForm
#print axioms norm_f_le_sharpClosedForm
#print axioms
  levelAlgebraicSourceRowError_le_exp_neg_three_quarters_of_closedForm

end Erdos240.BakerSourceAlgebraicUniformBounds
