/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAlgebraicUniformBounds
import ErdosProblems.Erdos240.BakerSourceAlgebraicStaticFactors
import ErdosProblems.Erdos240.BakerSourceBudgetInequalities
import ErdosProblems.Erdos240.BakerSourceInitialOuterBudget

/-!
# Closed source growth on the positive Lemma-4 contours

This file absorbs the source-faithful, level-scaled algebraic majorant on
the positive interpolation stages.  The sharp old-coordinate Delta estimate
is essential: it separates `(2 B)^S` from the binary side factor and hence
introduces no spurious logarithm of the varying height.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourcePositiveStageGrowth

open Finset
open Erdos240
open BakerLemma2Concrete
open BakerLemma3
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerSourceAlgebraicExponentAbsorption
open BakerSourceAlgebraicLevelMajorant
open BakerSourceAlgebraicMajorant
open BakerSourceAlgebraicMomentBounds
open BakerSourceAlgebraicUniformBounds
open BakerSourceAlgebraicStaticFactors
open BakerSourceMajorantClosedForm
open BakerSourceOversizedConstantNumerics
open BakerSourceState

/-- The common height unit in all source contour estimates. -/
def sourceHeightUnit {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℝ :=
  (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld

/-- The positive-stage head/rate unit. -/
def positiveStageHeightUnit {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (t : ℕ) : ℝ :=
  (P.h : ℝ) * P.k ^
      (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ)) *
    P.Omega * Real.log P.OmegaOld

theorem sourceHeightUnit_pos {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) : 0 < sourceHeightUnit P := by
  unfold sourceHeightUnit
  exact mul_pos
    (mul_pos (mul_pos (by exact_mod_cast P.h_pos) P.k_pos) P.Omega_pos)
    P.log_OmegaOld_pos

theorem positiveStageHeightUnit_pos {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (t : ℕ) :
    0 < positiveStageHeightUnit P t := by
  unfold positiveStageHeightUnit
  exact mul_pos
    (mul_pos
      (mul_pos (by exact_mod_cast P.h_pos)
        (Real.rpow_pos_of_pos P.k_pos _)) P.Omega_pos)
    P.log_OmegaOld_pos

theorem one_le_positiveStageHeightUnit {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (t : ℕ) :
    1 ≤ positiveStageHeightUnit P t := by
  have hexponent : 0 ≤
      1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ) := by
    have ht0 : (0 : ℝ) ≤ (t + 1 : ℕ) := by positivity
    nlinarith [P.sigma_add_epsilon_lt_one, P.epsilon_pos,
      mul_nonneg P.epsilon_pos.le ht0]
  have hk : 1 ≤ P.k ^
      (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ)) :=
    Real.one_le_rpow P.one_le_k hexponent
  have hh : (2 : ℝ) ≤ P.h := by exact_mod_cast P.two_le_h
  have hlog : (1 / 2 : ℝ) ≤ Real.log P.OmegaOld := by
    exact (by nlinarith [Real.log_two_gt_d9] :
      (1 / 2 : ℝ) ≤ Real.log 2).trans P.log_two_le_log_OmegaOld
  have hhk : (2 : ℝ) * 1 ≤ (P.h : ℝ) *
      P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ)) :=
    mul_le_mul hh hk (by norm_num) (by positivity)
  have hhkO : (2 : ℝ) * 1 * 1 ≤ (P.h : ℝ) *
      P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ)) * P.Omega :=
    mul_le_mul hhk P.one_le_Omega (by norm_num)
      (mul_nonneg (by positivity) (Real.rpow_pos_of_pos P.k_pos _).le)
  unfold positiveStageHeightUnit
  calc
    (1 : ℝ) = 2 * 1 * 1 * (1 / 2) := by ring
    _ ≤ (P.h : ℝ) *
        P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ)) *
        P.Omega * Real.log P.OmegaOld :=
      mul_le_mul hhkO hlog (by norm_num)
        (mul_nonneg
          (mul_nonneg (by positivity) (Real.rpow_pos_of_pos P.k_pos _).le)
          P.Omega_pos.le)

/-- Every positive interpolation stage has at most half the initial
derivative budget. -/
theorem lemmaFourBudget_succ_cast_le_half_levelScale {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank))
    (N t : ℕ) :
    (P.lemmaFourBudget N (t + 1) : ℝ) ≤ P.levelScale N / 2 := by
  have hnat : P.lemmaFourBudget N (t + 1) ≤ P.lemmaFourBudget N 1 := by
    induction t with
    | zero => simp
    | succ t ih =>
        exact (P.lemmaFourBudget_succ_le_current N (t + 1)).trans ih
  calc
    (P.lemmaFourBudget N (t + 1) : ℝ) ≤
        (P.lemmaFourBudget N 1 : ℝ) := by exact_mod_cast hnat
    _ = (⌊(P.Slevel N : ℝ) / 2⌋₊ : ℕ) := by
      rw [P.lemmaFourBudget_one]
    _ ≤ (P.Slevel N : ℝ) / 2 := by
      exact Nat.floor_le (by positivity)
    _ ≤ P.levelScale N / 2 := by
      gcongr
      exact P.Slevel_cast_le N

/-- The source cutoff satisfies the convenient logarithmic inequality
`log (2 B) ≤ 2h`. -/
theorem log_two_mul_Bsrc_le_two_h {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    Real.log (2 * (P.Bsrc : ℝ)) ≤ 2 * P.h := by
  have hBpos : (0 : ℝ) < P.Bsrc :=
    (Real.exp_pos 2).trans_le P.Bsrc_lower
  have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hBpos.ne']
  have hh : (2 : ℝ) ≤ P.h := by exact_mod_cast P.two_le_h
  nlinarith [P.log_Bsrc_lt_h_add_one]

/-- The sharp `(2B)^S` part of the old-coordinate Delta product consumes at
most one unscaled source height unit at every positive stage. -/
theorem oldDeltaPower_le_exp_sourceHeightUnit {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank))
    (N t : ℕ) :
    (((2 * P.Bsrc : ℕ) : ℝ) ^ P.lemmaFourBudget N (t + 1)) ≤
      Real.exp (sourceHeightUnit P) := by
  have hBpos : 0 < P.Bsrc := by
    have : (0 : ℝ) < P.Bsrc :=
      (Real.exp_pos 2).trans_le P.Bsrc_lower
    exact_mod_cast this
  apply VDPLParameters.pow_le_exp_of_mul_log_le (by positivity)
  have hbudget := lemmaFourBudget_succ_cast_le_half_levelScale P N t
  have hlog := log_two_mul_Bsrc_le_two_h P
  have hlognonneg : 0 ≤ Real.log (((2 * P.Bsrc : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    have hB : 1 ≤ P.Bsrc := by
      have hBreal : (1 : ℝ) ≤ P.Bsrc :=
        (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans P.Bsrc_lower
      exact_mod_cast hBreal
    exact_mod_cast (show 1 ≤ 2 * P.Bsrc by omega)
  have hlog' : Real.log (((2 * P.Bsrc : ℕ) : ℝ)) ≤ 2 * P.h := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlog
  calc
    (P.lemmaFourBudget N (t + 1) : ℝ) *
        Real.log (((2 * P.Bsrc : ℕ) : ℝ)) ≤
      (P.levelScale N / 2) * (2 * P.h) :=
        mul_le_mul hbudget hlog' hlognonneg
          (div_nonneg (P.levelScale_pos N).le (by norm_num))
    _ = P.levelScale N * P.h := by ring
    _ ≤ sourceHeightUnit P := by
      unfold sourceHeightUnit VDPLParameters.levelScale
      have hq : P.qInvPow N ≤ 1 := by
        have h := P.qInvPow_antitone (Nat.zero_le N)
        simpa [VDPLParameters.qInvPow] using h
      have hrest : 0 ≤ P.k * P.Omega * Real.log P.OmegaOld :=
        mul_nonneg (mul_nonneg P.k_pos.le P.Omega_pos.le)
          P.log_OmegaOld_pos.le
      have hscaled :
          P.qInvPow N * (P.k * P.Omega * Real.log P.OmegaOld) ≤
            1 * (P.k * P.Omega * Real.log P.OmegaOld) :=
        mul_le_mul_of_nonneg_right hq hrest
      have hh : (0 : ℝ) ≤ P.h := by positivity
      calc
        P.qInvPow N * P.k * P.Omega * Real.log P.OmegaOld * P.h =
            (P.qInvPow N *
              (P.k * P.Omega * Real.log P.OmegaOld)) * P.h := by ring
        _ ≤ (1 * (P.k * P.Omega * Real.log P.OmegaOld)) * P.h :=
          mul_le_mul_of_nonneg_right hscaled hh
        _ = (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld := by ring

/-- Each old algebraic logarithm is bounded by its normalized source
height logarithm. -/
theorem norm_oldLog_le_log_oldHeight {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (r : Fin oldRank) :
    ‖oldLog P r‖ ≤ Real.log (P.oldHeight r) := by
  unfold oldLog
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
  · exact Real.log_le_log (by exact_mod_cast P.old_prime r |>.pos)
      (P.old_cast_lt_oldHeight r).le
  · exact Real.log_pos (by exact_mod_cast (P.old_prime r).one_lt)

/-- The varying algebraic logarithm is bounded by the distinguished largest
source height. -/
theorem norm_lastLog_le_log_newHeight {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    ‖lastLog P‖ ≤ Real.log P.newHeight := by
  unfold lastLog
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
  · apply Real.log_le_log (by exact_mod_cast P.newPrime_pos)
    exact P.newPrime_cast_lt_varyingHeight.le.trans
      P.varyingHeight_le_newHeight
  · exact Real.log_pos (by exact_mod_cast P.new_prime.one_lt)

/-- The unscaled algebraic rate has exactly the source's one-eighth height
budget. -/
theorem sourceAlgebraicRateBound_le_eighth {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    sourceAlgebraicRateBound P ≤
      (1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld := by
  let U : ℝ := (8 * P.rank : ℝ)⁻¹ * P.k ^ (1 - P.sigma) *
    P.Omega * Real.log P.OmegaOld
  have hterm (r : Fin oldRank) :
      (P.LiZero r : ℝ) * ‖oldLog P r‖ ≤ U := by
    calc
      (P.LiZero r : ℝ) * ‖oldLog P r‖ ≤
          P.LiZeroScale r * Real.log (P.oldHeight r) :=
        mul_le_mul (P.LiZero_cast_le r)
          (norm_oldLog_le_log_oldHeight P r) (norm_nonneg _)
          (P.LiZeroScale_pos r).le
      _ = U := by
        dsimp only [U]
        unfold VDPLParameters.LiZeroScale
        field_simp [P.log_oldHeight_pos r |>.ne']
  have hlast :
      (P.LlastZero : ℝ) * ‖lastLog P‖ ≤ U := by
    calc
      (P.LlastZero : ℝ) * ‖lastLog P‖ ≤
          P.LlastZeroScale * Real.log P.newHeight :=
        mul_le_mul P.LlastZero_cast_le
          (norm_lastLog_le_log_newHeight P) (norm_nonneg _)
          P.LlastZeroScale_pos.le
      _ = U := by
        dsimp only [U]
        unfold VDPLParameters.LlastZeroScale
        field_simp [P.log_newHeight_pos.ne']
  unfold sourceAlgebraicRateBound
  calc
    (∑ r : Fin oldRank, (P.LiZero r : ℝ) * ‖oldLog P r‖) +
        (P.LlastZero : ℝ) * ‖lastLog P‖ ≤
      (∑ _r : Fin oldRank, U) + U :=
        add_le_add (Finset.sum_le_sum fun r _hr ↦ hterm r) hlast
    _ = (P.rank : ℝ) * U := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp only [Fintype.card_fin, VDPLParameters.rank]
      push_cast
      ring
    _ = (1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
        Real.log P.OmegaOld := by
      dsimp only [U]
      have hrankPos : (0 : ℝ) < P.rank := by exact_mod_cast P.rank_pos
      have hrank : (P.rank : ℝ) ≠ 0 := ne_of_gt hrankPos
      field_simp

/-- On the positive Lemma-4 contour the level-scaled argument has no
remaining `q^N` factor. -/
theorem norm_scaledArgument_le_positiveContour {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank))
    (N t : ℕ) (z : ℂ)
    (hz : ‖z‖ = 3 * P.lemmaFourRadius N (t + 1)) :
    ‖scaledArgument P.q N z‖ ≤
      48 * P.h * P.k ^ (P.epsilon * ((t + 1 : ℕ) : ℝ)) := by
  unfold scaledArgument
  rw [norm_div, norm_pow, Complex.norm_natCast]
  have hqpow : (0 : ℝ) < (P.q : ℝ) ^ N := by
    exact_mod_cast pow_pos (Nat.zero_lt_of_lt P.one_lt_q) N
  rw [div_le_iff₀ hqpow]
  have hR : (P.lemmaFourRadius N (t + 1) : ℝ) ≤
      P.lemmaFourRadiusScale N (t + 1) :=
    Nat.floor_le (P.lemmaFourRadiusScale_pos N (t + 1)).le
  calc
    ‖z‖ = 3 * (P.lemmaFourRadius N (t + 1) : ℝ) := hz
    _ ≤ 3 * P.lemmaFourRadiusScale N (t + 1) := by gcongr
    _ = (48 * P.h *
          P.k ^ (P.epsilon * ((t + 1 : ℕ) : ℝ))) *
        (P.q : ℝ) ^ N := by
      unfold VDPLParameters.lemmaFourRadiusScale
      push_cast
      ring

theorem one_le_stageRadiusPower {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (t : ℕ) :
    1 ≤ P.k ^ (P.epsilon * ((t + 1 : ℕ) : ℝ)) := by
  apply Real.one_le_rpow P.one_le_k
  exact mul_nonneg P.epsilon_pos.le (Nat.cast_nonneg _)

/-- The binary side part of the sharp old-coordinate Delta estimate costs
at most one positive-stage unit. -/
theorem oldDeltaSidePower_le_exp_positiveStageHeightUnit {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank))
    (N t : ℕ) :
    (2 : ℝ) ^ levelOldDeltaSideSum P N ≤
      Real.exp (positiveStageHeightUnit P t) := by
  apply VDPLParameters.pow_le_exp_of_mul_log_le (by norm_num)
  have hside := levelOldDeltaSideSum_cast_le P N
  have hq : P.qInvPow N ≤ 1 := by
    have h := P.qInvPow_antitone (Nat.zero_le N)
    simpa [VDPLParameters.qInvPow] using h
  have hcore : 0 ≤ (1 / 4 : ℝ) * P.k ^ (1 - P.sigma) *
      P.Omega * Real.log P.OmegaOld := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg P.k_pos.le _))
        P.Omega_pos.le) P.log_OmegaOld_pos.le
  have hside' : (levelOldDeltaSideSum P N : ℝ) ≤
      (1 / 4 : ℝ) * P.k ^ (1 - P.sigma) *
        P.Omega * Real.log P.OmegaOld := by
    exact hside.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hq hcore)
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hsideNonneg : (0 : ℝ) ≤ levelOldDeltaSideSum P N := by positivity
  calc
    (levelOldDeltaSideSum P N : ℝ) * Real.log 2 ≤
        (levelOldDeltaSideSum P N : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hlog hsideNonneg
    _ ≤ (1 / 4 : ℝ) * P.k ^ (1 - P.sigma) *
        P.Omega * Real.log P.OmegaOld := by simpa using hside'
    _ ≤ positiveStageHeightUnit P t := by
      unfold positiveStageHeightUnit
      rw [show 1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ) =
        (1 - P.sigma) + P.epsilon * ((t + 1 : ℕ) : ℝ) by ring,
        Real.rpow_add P.k_pos]
      have hhK : (1 / 4 : ℝ) ≤
          (P.h : ℝ) * P.k ^ (P.epsilon * ((t + 1 : ℕ) : ℝ)) := by
        have hh : (2 : ℝ) ≤ P.h := by exact_mod_cast P.two_le_h
        have hK := one_le_stageRadiusPower P t
        nlinarith [mul_le_mul hh hK (by norm_num : (0 : ℝ) ≤ 1)
          (by positivity : (0 : ℝ) ≤ (P.h : ℝ))]
      have hrest : 0 ≤ P.k ^ (1 - P.sigma) * P.Omega *
          Real.log P.OmegaOld := by
        exact mul_nonneg
          (mul_nonneg (Real.rpow_nonneg P.k_pos.le _) P.Omega_pos.le)
          P.log_OmegaOld_pos.le
      calc
        (1 / 4 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
            Real.log P.OmegaOld =
          (1 / 4 : ℝ) * (P.k ^ (1 - P.sigma) * P.Omega *
            Real.log P.OmegaOld) := by ring
        _ ≤ ((P.h : ℝ) *
            P.k ^ (P.epsilon * ((t + 1 : ℕ) : ℝ))) *
            (P.k ^ (1 - P.sigma) * P.Omega *
              Real.log P.OmegaOld) :=
          mul_le_mul_of_nonneg_right hhK hrest
        _ = (P.h : ℝ) *
            (P.k ^ (1 - P.sigma) *
              P.k ^ (P.epsilon * ((t + 1 : ℕ) : ℝ))) *
            P.Omega * Real.log P.OmegaOld := by ring

/-- The level-scaled algebraic exponential costs six positive-stage units
on the outer contour. -/
theorem algebraicRateExponent_le_six_positiveStageHeightUnit
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (N t : ℕ) (z : ℂ)
    (hz : ‖z‖ = 3 * P.lemmaFourRadius N (t + 1)) :
    P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖ ≤
      6 * positiveStageHeightUnit P t := by
  have hq : 0 ≤ P.qInvPow N := (P.qInvPow_pos N).le
  have hrate := sourceAlgebraicRateBound_le_eighth P
  have hz' := norm_scaledArgument_le_positiveContour P N t z hz
  have hscaled : P.qInvPow N * ‖z‖ =
      ‖scaledArgument P.q N z‖ := by
    unfold scaledArgument VDPLParameters.qInvPow
    rw [norm_div, norm_pow, Complex.norm_natCast]
    rw [Nat.cast_pow]
    field_simp
  calc
    P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖ =
        sourceAlgebraicRateBound P * (P.qInvPow N * ‖z‖) := by ring
    _ = sourceAlgebraicRateBound P * ‖scaledArgument P.q N z‖ := by
      rw [hscaled]
    _ ≤
        ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
          Real.log P.OmegaOld) *
        (48 * P.h * P.k ^
          (P.epsilon * ((t + 1 : ℕ) : ℝ))) :=
      mul_le_mul hrate hz' (norm_nonneg _)
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) (Real.rpow_nonneg P.k_pos.le _))
            P.Omega_pos.le) P.log_OmegaOld_pos.le)
    _ = 6 * positiveStageHeightUnit P t := by
      unfold positiveStageHeightUnit
      rw [show 1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ) =
        (1 - P.sigma) + P.epsilon * ((t + 1 : ℕ) : ℝ) by ring,
        Real.rpow_add P.k_pos]
      ring

/-- The powered head-Delta factor costs eight positive-stage units on the
outer contour.  The ceiling and both successor terms are included. -/
theorem sourceHeadDeltaMajorant_le_exp_eight_positiveStageHeightUnit
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (N t : ℕ) (z : ℂ)
    (hz : ‖z‖ = 3 * P.lemmaFourRadius N (t + 1)) :
    sourceHeadDeltaMajorant P N z ≤
      Real.exp (8 * positiveStageHeightUnit P t) := by
  let K : ℝ := P.k ^ (P.epsilon * ((t + 1 : ℕ) : ℝ))
  let x : ℝ := 48 * P.h * K
  have hzScaled : ‖scaledArgument P.q N z‖ ≤ x := by
    simpa only [x, K] using
      norm_scaledArgument_le_positiveContour P N t z hz
  refine (sourceHeadDeltaMajorant_le_of_scaledNorm_le
    P N z hzScaled).trans ?_
  apply VDPLParameters.pow_le_exp_of_mul_log_le (by norm_num)
  have hh : (2 : ℝ) ≤ P.h := by exact_mod_cast P.two_le_h
  have hK : 1 ≤ K := by
    simpa only [K] using one_le_stageRadiusPower P t
  have hh0 : (0 : ℝ) ≤ P.h := by positivity
  have hK0 : 0 ≤ K := hK.trans' (by norm_num)
  have hhK : (P.h : ℝ) ≤ P.h * K := by
    nlinarith [mul_le_mul_of_nonneg_left hK hh0]
  have htwo : (2 : ℝ) ≤ P.h * K := hh.trans hhK
  have hx0 : 0 ≤ x + P.h := by
    dsimp only [x]
    positivity
  have hceil : (Nat.ceil (x + P.h) : ℝ) < x + P.h + 1 :=
    Nat.ceil_lt_add_one hx0
  have hcount :
      ((Nat.ceil (x + P.h) + 1 + P.h : ℕ) : ℝ) ≤
        64 * P.h * K := by
    push_cast
    dsimp only [x] at hceil ⊢
    nlinarith
  have hL := P.LzeroPlusOne_cast_le
  have hcountL :
      (((Nat.ceil (x + P.h) + 1 + P.h) * P.LzeroPlusOne : ℕ) : ℝ) ≤
        (64 * P.h * K) * P.LzeroScale := by
    push_cast
    have hcount' : (Nat.ceil (x + P.h) : ℝ) + 1 + P.h ≤
        64 * P.h * K := by
      simpa only [Nat.cast_add, Nat.cast_one] using hcount
    exact mul_le_mul hcount' hL (Nat.cast_nonneg _)
      (by positivity)
  have hlog : Real.log (2 : ℝ) ≤ Real.log P.OmegaOld :=
    P.log_two_le_log_OmegaOld
  have hlog0 : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num)
  calc
    (((Nat.ceil (x + P.h) + 1 + P.h) * P.LzeroPlusOne : ℕ) : ℝ) *
        Real.log 2 ≤
      ((64 * P.h * K) * P.LzeroScale) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hcountL hlog0
    _ ≤ ((64 * P.h * K) * P.LzeroScale) *
        Real.log P.OmegaOld := by
      exact mul_le_mul_of_nonneg_left hlog
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hh0) hK0)
          (by
            unfold VDPLParameters.LzeroScale
            exact mul_nonneg
              (mul_nonneg (by norm_num)
                (Real.rpow_pos_of_pos P.k_pos _).le)
              P.Omega_pos.le))
    _ = 8 * positiveStageHeightUnit P t := by
      unfold VDPLParameters.LzeroScale positiveStageHeightUnit
      dsimp only [K]
      rw [show 1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ) =
        (1 - P.sigma) + P.epsilon * ((t + 1 : ℕ) : ℝ) by ring,
        Real.rpow_add P.k_pos]
      ring

/-- The complete sharp algebraic growth envelope on a positive Lemma-4
contour, with the exact `5H/3 + 15 H_t` internal ledger exposed. -/
theorem sourceSharpAlgebraicGrowthMajorant_le_positiveContour
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    (N t : ℕ) (z : ℂ)
    (hz : ‖z‖ = 3 * P.lemmaFourRadius N (t + 1)) :
    sourceSharpAlgebraicGrowthMajorant P N z
        (P.lemmaFourBudget N (t + 1)) ≤
      Real.exp ((5 / 3 : ℝ) * sourceHeightUnit P +
        15 * positiveStageHeightUnit P t) := by
  let H : ℝ := sourceHeightUnit P
  let T : ℝ := positiveStageHeightUnit P t
  have hstatic := support_sq_mul_coeffHeight_le_exp_two_thirds P hreq
  have hold := oldDeltaPower_le_exp_sourceHeightUnit P N t
  have hside := oldDeltaSidePower_le_exp_positiveStageHeightUnit P N t
  have hhead :=
    sourceHeadDeltaMajorant_le_exp_eight_positiveStageHeightUnit P N t z hz
  have hrate :
      Real.exp (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖) ≤
        Real.exp (6 * T) := by
    apply Real.exp_le_exp.mpr
    simpa only [T] using
      algebraicRateExponent_le_six_positiveStageHeightUnit P N t z hz
  have hold0 : 0 ≤ (((2 * P.Bsrc : ℕ) : ℝ) ^
      P.lemmaFourBudget N (t + 1)) := by positivity
  have hhead0 : 0 ≤ sourceHeadDeltaMajorant P N z := by
    unfold sourceHeadDeltaMajorant
    positivity
  have hside0 : 0 ≤ (2 : ℝ) ^ levelOldDeltaSideSum P N := by positivity
  have hrate0 : 0 ≤ Real.exp
      (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖) :=
    (Real.exp_pos _).le
  have hH : 0 ≤ H := (sourceHeightUnit_pos P).le
  have hraw :
      sourceSharpAlgebraicGrowthMajorant P N z
          (P.lemmaFourBudget N (t + 1)) ≤
        Real.exp ((2 / 3 : ℝ) * H) * Real.exp H *
          Real.exp (8 * T) * Real.exp T * Real.exp (6 * T) := by
    unfold sourceSharpAlgebraicGrowthMajorant
      sourceSharpDeltaFactorMajorant
    calc
      (initialSupportBound P : ℝ) *
          (P.coeffHeight *
            ((initialSupportBound P : ℝ) *
              (sourceHeadDeltaMajorant P N z *
                (((2 * P.Bsrc : ℕ) : ℝ) ^
                    P.lemmaFourBudget N (t + 1) *
                  (2 : ℝ) ^ levelOldDeltaSideSum P N)))) *
          Real.exp (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖) =
        ((initialSupportBound P : ℝ) *
          (P.coeffHeight * (initialSupportBound P : ℝ))) *
          (((((2 * P.Bsrc : ℕ) : ℝ) ^
              P.lemmaFourBudget N (t + 1)) *
            sourceHeadDeltaMajorant P N z) *
            (2 : ℝ) ^ levelOldDeltaSideSum P N) *
          Real.exp (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖) := by
            ring
      _ ≤ Real.exp ((2 / 3 : ℝ) * H) *
          ((Real.exp H * Real.exp (8 * T)) * Real.exp T) *
          Real.exp (6 * T) := by
        have hs : (initialSupportBound P : ℝ) *
            (P.coeffHeight * (initialSupportBound P : ℝ)) ≤
              Real.exp ((2 / 3 : ℝ) * H) := by
          simpa only [H, sourceHeightUnit] using hstatic
        have ho : (((2 * P.Bsrc : ℕ) : ℝ) ^
            P.lemmaFourBudget N (t + 1)) ≤ Real.exp H := by
          simpa only [H] using hold
        have hh : sourceHeadDeltaMajorant P N z ≤ Real.exp (8 * T) := by
          simpa only [T] using hhead
        have hd : (2 : ℝ) ^ levelOldDeltaSideSum P N ≤ Real.exp T := by
          simpa only [T] using hside
        have hoh : (((2 * P.Bsrc : ℕ) : ℝ) ^
              P.lemmaFourBudget N (t + 1)) *
              sourceHeadDeltaMajorant P N z ≤
            Real.exp H * Real.exp (8 * T) :=
          mul_le_mul ho hh hhead0 (Real.exp_pos H).le
        have hohd : ((((2 * P.Bsrc : ℕ) : ℝ) ^
              P.lemmaFourBudget N (t + 1)) *
              sourceHeadDeltaMajorant P N z) *
              (2 : ℝ) ^ levelOldDeltaSideSum P N ≤
            (Real.exp H * Real.exp (8 * T)) * Real.exp T :=
          mul_le_mul hoh hd hside0
            (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
        have hdyn : (((((2 * P.Bsrc : ℕ) : ℝ) ^
                P.lemmaFourBudget N (t + 1)) *
                sourceHeadDeltaMajorant P N z) *
                (2 : ℝ) ^ levelOldDeltaSideSum P N) *
                Real.exp (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖) ≤
              ((Real.exp H * Real.exp (8 * T)) * Real.exp T) *
                Real.exp (6 * T) :=
          mul_le_mul hohd hrate hrate0
            (mul_nonneg
              (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
              (Real.exp_pos _).le)
        calc
          ((initialSupportBound P : ℝ) *
                (P.coeffHeight * (initialSupportBound P : ℝ))) *
              (((((2 * P.Bsrc : ℕ) : ℝ) ^
                  P.lemmaFourBudget N (t + 1)) *
                sourceHeadDeltaMajorant P N z) *
                (2 : ℝ) ^ levelOldDeltaSideSum P N) *
              Real.exp
                (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖) =
            ((initialSupportBound P : ℝ) *
                (P.coeffHeight * (initialSupportBound P : ℝ))) *
              ((((((2 * P.Bsrc : ℕ) : ℝ) ^
                    P.lemmaFourBudget N (t + 1)) *
                  sourceHeadDeltaMajorant P N z) *
                  (2 : ℝ) ^ levelOldDeltaSideSum P N) *
                Real.exp
                  (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖)) := by
                    ring
          _ ≤ Real.exp ((2 / 3 : ℝ) * H) *
              ((((((2 * P.Bsrc : ℕ) : ℝ) ^
                    P.lemmaFourBudget N (t + 1)) *
                  sourceHeadDeltaMajorant P N z) *
                  (2 : ℝ) ^ levelOldDeltaSideSum P N) *
                Real.exp
                  (P.qInvPow N * sourceAlgebraicRateBound P * ‖z‖)) :=
            mul_le_mul_of_nonneg_right hs
              (mul_nonneg
                (mul_nonneg (mul_nonneg hold0 hhead0) hside0) hrate0)
          _ ≤ Real.exp ((2 / 3 : ℝ) * H) *
              (((Real.exp H * Real.exp (8 * T)) * Real.exp T) *
                Real.exp (6 * T)) :=
            mul_le_mul_of_nonneg_left hdyn (Real.exp_pos _).le
          _ = Real.exp ((2 / 3 : ℝ) * H) *
              ((Real.exp H * Real.exp (8 * T)) * Real.exp T) *
              Real.exp (6 * T) := by ring
      _ = Real.exp ((2 / 3 : ℝ) * H) * Real.exp H *
          Real.exp (8 * T) * Real.exp T * Real.exp (6 * T) := by ring
  calc
    sourceSharpAlgebraicGrowthMajorant P N z
        (P.lemmaFourBudget N (t + 1)) ≤
      Real.exp ((2 / 3 : ℝ) * H) * Real.exp H *
        Real.exp (8 * T) * Real.exp T * Real.exp (6 * T) := hraw
    _ = Real.exp (((2 / 3 : ℝ) * H) + H + 8 * T + T + 6 * T) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ = Real.exp ((5 / 3 : ℝ) * H + 15 * T) := by
      congr 1
      ring
    _ = Real.exp ((5 / 3 : ℝ) * sourceHeightUnit P +
        15 * positiveStageHeightUnit P t) := by rfl

/-- Once the closed scaled amplification has the standard structural
quarter-exponent bound, the normalized logarithmic form makes its literal
perturbation exponent smaller than one (hence than nine stage units). -/
theorem closedAmplification_mul_smallLinearFormBound_le_nine_stageUnits
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (N t : ℕ) (z : ℂ)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hamplification :
      (initialSupportBound P : ℝ) *
          (P.qInvPow N * P.LlastZero) * ‖z‖ ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4)) :
    ((initialSupportBound P : ℝ) *
        (P.qInvPow N * P.LlastZero) * ‖z‖) *
        smallLinearFormBound P (C₀ * Real.log P.OmegaOld) ≤
      9 * positiveStageHeightUnit P t := by
  let E : ℝ := sourceExponent P (C₀ * Real.log P.OmegaOld)
  let A : ℝ := (initialSupportBound P : ℝ) *
    (P.qInvPow N * P.LlastZero) * ‖z‖
  have hE0 : 0 ≤ E := by dsimp only [E]; linarith
  have hA : A ≤ Real.exp (E / 16) := by
    exact hamplification.trans
      (by
        simpa only [E] using
          exp_quarter_le_exp_sixteenth_of_four_mul_le P hstruct)
  have hsmallEq : smallLinearFormBound P
      (C₀ * Real.log P.OmegaOld) = Real.exp (-E) := by
    rfl
  have hprod : A * smallLinearFormBound P
      (C₀ * Real.log P.OmegaOld) ≤ 1 := by
    rw [hsmallEq]
    calc
      A * Real.exp (-E) ≤ Real.exp (E / 16) * Real.exp (-E) :=
        mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
      _ = Real.exp (-15 * E / 16) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith)
      _ = 1 := Real.exp_zero
  exact hprod.trans (by
    have hT := one_le_positiveStageHeightUnit P t
    nlinarith)

/-- Direct analytic closed form on a positive Lemma-4 contour. -/
theorem sourceSharpAnalyticGrowthMajorant_le_positiveContour
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    (N t : ℕ) (z : ℂ)
    (hz : ‖z‖ = 3 * P.lemmaFourRadius N (t + 1))
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hamplification :
      (initialSupportBound P : ℝ) *
          (P.qInvPow N * P.LlastZero) * ‖z‖ ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4)) :
    sourceSharpAnalyticGrowthMajorant P N z
        (P.lemmaFourBudget N (t + 1))
        (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) ≤
      Real.exp ((5 / 3 : ℝ) * sourceHeightUnit P +
        24 * positiveStageHeightUnit P t) := by
  have hgrowth := sourceSharpAlgebraicGrowthMajorant_le_positiveContour
    P hreq N t z hz
  have hperturb :=
    closedAmplification_mul_smallLinearFormBound_le_nine_stageUnits
      P N t z hstruct hE hamplification
  unfold sourceSharpAnalyticGrowthMajorant
  calc
    sourceSharpAlgebraicGrowthMajorant P N z
          (P.lemmaFourBudget N (t + 1)) *
        Real.exp (((initialSupportBound P : ℝ) *
          (P.qInvPow N * P.LlastZero) * ‖z‖) *
            smallLinearFormBound P
              (C₀ * Real.log P.OmegaOld)) ≤
      Real.exp ((5 / 3 : ℝ) * sourceHeightUnit P +
          15 * positiveStageHeightUnit P t) *
        Real.exp (9 * positiveStageHeightUnit P t) := by
      exact mul_le_mul hgrowth (Real.exp_le_exp.mpr hperturb)
        (Real.exp_pos _).le
        (Real.exp_pos _).le
    _ = Real.exp ((5 / 3 : ℝ) * sourceHeightUnit P +
        24 * positiveStageHeightUnit P t) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- At the exceptional `t = 0` contour, the source's third p.39
requirement absorbs all twenty-four varying-stage units into the remaining
one-third fixed-height reserve. -/
theorem sourceSharpAnalyticGrowthMajorant_le_zeroContour
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hunknown : initialUnknownRequirement P ∈ P.kRequirements)
    (hsourceTen : P.sourceTenThreshold ∈ P.kRequirements)
    (N : ℕ) (z : ℂ)
    (hz : ‖z‖ = 3 * P.lemmaFourRadius N 1)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hamplification :
      (initialSupportBound P : ℝ) *
          (P.qInvPow N * P.LlastZero) * ‖z‖ ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4)) :
    sourceSharpAnalyticGrowthMajorant P N z
        (P.lemmaFourBudget N 1)
        (smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) ≤
      Real.exp (2 * sourceHeightUnit P) := by
  have hbase := sourceSharpAnalyticGrowthMajorant_le_positiveContour
    P hunknown N 0 z (by simpa using hz) hstruct hE hamplification
  have hKraw :=
    P.thirtyTwo_mul_initialStagePower_lt_four_fifteenths_mul_k hsourceTen
  have hK : 24 * P.k ^ (1 - P.sigma + P.epsilon) ≤
      (1 / 5 : ℝ) * P.k := by
    linarith
  have hfactor : 0 ≤
      (P.h : ℝ) * P.Omega * Real.log P.OmegaOld := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) P.Omega_pos.le)
      P.log_OmegaOld_pos.le
  have hstage : 24 * positiveStageHeightUnit P 0 ≤
      (1 / 5 : ℝ) * sourceHeightUnit P := by
    calc
      24 * positiveStageHeightUnit P 0 =
          (24 * P.k ^ (1 - P.sigma + P.epsilon)) *
            ((P.h : ℝ) * P.Omega * Real.log P.OmegaOld) := by
        unfold positiveStageHeightUnit
        norm_num
        ring
      _ ≤ ((1 / 5 : ℝ) * P.k) *
          ((P.h : ℝ) * P.Omega * Real.log P.OmegaOld) :=
        mul_le_mul_of_nonneg_right hK hfactor
      _ = (1 / 5 : ℝ) * sourceHeightUnit P := by
        unfold sourceHeightUnit
        ring
  refine hbase.trans (Real.exp_le_exp.mpr ?_)
  have hH := (sourceHeightUnit_pos P).le
  linarith

/-- Actual auxiliary-function estimate for the exceptional first contour. -/
theorem norm_f_le_zeroContour {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hunknown : initialUnknownRequirement P ∈ P.kRequirements)
    (hsourceTen : P.sourceTenThreshold ∈ P.kRequirements)
    {N : ℕ} (state : LevelState P N) (b : Fin oldRank → ℤ)
    {bLast : ℤ} (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    (z : ℂ) (hz : ‖z‖ = 3 * P.lemmaFourRadius N 1)
    (m : VDPLMultiIndex P.rank)
    (hm : VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N 1)
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hamplification :
      (initialSupportBound P : ℝ) *
          (P.qInvPow N * P.LlastZero) * ‖z‖ ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (hsmall : ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤
      smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) :
    ‖f state b bLast z m‖ ≤ Real.exp (2 * sourceHeightUnit P) := by
  refine (norm_f_le_sharpClosedForm P state b hb hbLastBound hbLast z m hm
    (by unfold smallLinearFormBound; positivity) hsmall).trans ?_
  exact sourceSharpAnalyticGrowthMajorant_le_zeroContour P hunknown
    hsourceTen N z hz hstruct hE hamplification

/-- Actual rank-indexed auxiliary-function boundary bound used by the
positive branch of the Lemma-4 callback. -/
theorem norm_f_le_positiveContour {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    {N : ℕ} (state : LevelState P N) (b : Fin oldRank → ℤ)
    {bLast : ℤ} (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLastBound : bLast.natAbs ≤ P.Bsrc) (hbLast : bLast ≠ 0)
    (t : ℕ) (z : ℂ)
    (hz : ‖z‖ = 3 * P.lemmaFourRadius N (t + 1))
    (m : VDPLMultiIndex P.rank)
    (hm : VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1))
    {C₀ : ℝ} (hstruct : 4 * P.C ≤ C₀)
    (hE : 8 ≤ sourceExponent P (C₀ * Real.log P.OmegaOld))
    (hamplification :
      (initialSupportBound P : ℝ) *
          (P.qInvPow N * P.LlastZero) * ‖z‖ ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4))
    (hsmall : ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤
      smallLinearFormBound P (C₀ * Real.log P.OmegaOld)) :
    ‖f state b bLast z m‖ ≤
      Real.exp (2 * sourceHeightUnit P +
        24 * positiveStageHeightUnit P t) := by
  refine (norm_f_le_sharpClosedForm P state b hb hbLastBound hbLast z m hm
    (by unfold smallLinearFormBound; positivity) hsmall).trans ?_
  refine (sourceSharpAnalyticGrowthMajorant_le_positiveContour
    P hreq N t z hz hstruct hE hamplification).trans ?_
  apply Real.exp_le_exp.mpr
  have hH := (sourceHeightUnit_pos P).le
  linarith

end Erdos240.BakerSourcePositiveStageGrowth

#print axioms
  Erdos240.BakerSourcePositiveStageGrowth.sourceSharpAlgebraicGrowthMajorant_le_positiveContour
#print axioms
  Erdos240.BakerSourcePositiveStageGrowth.norm_f_le_positiveContour
#print axioms
  Erdos240.BakerSourcePositiveStageGrowth.norm_f_le_zeroContour
