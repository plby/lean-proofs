/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceLiouvilleLowerBounds
import ErdosProblems.Erdos240.BakerSourceOversizedConstantUniform
import ErdosProblems.Erdos240.BakerSourceAlgebraicLevelMajorant

/-!
# Rational-target Liouville lower bounds

This file bounds the literal finite conjugate sum used in the rational
Liouville certificate.  The bound is uniform on the full Lemma-5 grid.
-/

open scoped BigOperators NumberField

noncomputable section

namespace Erdos240.BakerSourceRationalLiouvilleLowerBounds

open Erdos240
open BakerLemma3
open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerSourceLiouvilleLowerBounds
open BakerSourceAlgebraicLevelMajorant
open BakerSourceAlgebraicMajorant
open BakerSourceState
open BakerSourceOversizedConstantUniform

/-! ## Uniform bounds for radical monomials -/

theorem norm_embedding_radicalGenerator_pow {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (tau : SourceRadicalField P →ₐ[ℚ] ℂ) (i : Fin (oldRank + 1)) :
    ‖tau (radicalGenerator P i)‖ ^ 13 = (radicalPrime P i : ℝ) := by
  rw [← norm_pow, ← map_pow, radicalGenerator_pow]
  simp

theorem norm_embedding_radicalGenerator_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (tau : SourceRadicalField P →ₐ[ℚ] ℂ) (i : Fin (oldRank + 1))
    {A : ℝ} (hA : 1 ≤ A) (hprime : (radicalPrime P i : ℝ) ≤ A) :
    ‖tau (radicalGenerator P i)‖ ≤ A := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity : 0 ≤ A)
    (by norm_num : (13 : ℕ) ≠ 0)]
  rw [norm_embedding_radicalGenerator_pow]
  exact hprime.trans (by
    calc
      A ≤ A ^ 1 := by simp
      _ ≤ A ^ 13 := pow_le_pow_right₀ hA (by norm_num))

theorem norm_embedding_oldRadicalGenerator_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (tau : SourceRadicalField P →ₐ[ℚ] ℂ) (r : Fin oldRank) :
    ‖tau (radicalGenerator P r.castSucc)‖ ≤ P.oldHeight r := by
  apply norm_embedding_radicalGenerator_le P tau r.castSucc
  · exact (by norm_num : (1 : ℝ) ≤ Real.exp 2).trans
      (P.oldHeight_lower r)
  · simp only [radicalPrime_castSucc]
    exact (P.old_cast_lt_oldHeight r).le

theorem norm_embedding_lastRadicalGenerator_le {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (tau : SourceRadicalField P →ₐ[ℚ] ℂ) :
    ‖tau (radicalGenerator P (Fin.last oldRank))‖ ≤ P.newHeight := by
  apply norm_embedding_radicalGenerator_le P tau (Fin.last oldRank)
  · exact P.one_lt_newHeight.le
  · simp only [radicalPrime_last]
    exact P.newPrime_cast_lt_varyingHeight.le.trans
      P.varyingHeight_le_newHeight

theorem state_weightedExponentLogSum_le {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (lambda : LevelIndex P J) :
    (∑ r : Fin oldRank,
        ((coordinatesForState state).oldExponent lambda r : ℝ) *
          Real.log (P.oldHeight r)) +
      ((coordinatesForState state).lastExponent lambda : ℝ) *
          Real.log P.newHeight ≤
    P.qInvPow J * ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
      Real.log P.OmegaOld) := by
  have hold (r : Fin oldRank) :
      ((coordinatesForState state).oldExponent lambda r : ℝ) ≤
        P.qInvPow J * P.LiZero r := by
    calc
      ((coordinatesForState state).oldExponent lambda r : ℝ) ≤
          ((levelBoxShape P J).oldMax r : ℝ) := by
        exact_mod_cast Nat.le_of_lt_succ (lambda.oldExponentFin r).isLt
      _ ≤ P.qInvPow J * P.LiZero r :=
        scaledExponentMax_cast_le P J (P.LiZero r)
  have hlast :
      ((coordinatesForState state).lastExponent lambda : ℝ) ≤
        P.qInvPow J * P.LlastZero := by
    calc
      ((coordinatesForState state).lastExponent lambda : ℝ) ≤
          ((levelBoxShape P J).lastMax : ℝ) := by
        exact_mod_cast Nat.le_of_lt_succ lambda.lastExponentFin.isLt
      _ ≤ P.qInvPow J * P.LlastZero :=
        scaledExponentMax_cast_le P J P.LlastZero
  calc
    (∑ r : Fin oldRank,
        ((coordinatesForState state).oldExponent lambda r : ℝ) *
          Real.log (P.oldHeight r)) +
      ((coordinatesForState state).lastExponent lambda : ℝ) *
          Real.log P.newHeight ≤
        (∑ r : Fin oldRank,
          (P.qInvPow J * P.LiZero r) * Real.log (P.oldHeight r)) +
          (P.qInvPow J * P.LlastZero) * Real.log P.newHeight := by
      exact add_le_add
        (Finset.sum_le_sum fun r _hr ↦
          mul_le_mul_of_nonneg_right (hold r) (P.log_oldHeight_pos r).le)
        (mul_le_mul_of_nonneg_right hlast P.log_newHeight_pos.le)
    _ = P.qInvPow J *
        ((∑ r : Fin oldRank,
          (P.LiZero r : ℝ) * Real.log (P.oldHeight r)) +
          (P.LlastZero : ℝ) * Real.log P.newHeight) := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      ring
    _ ≤ P.qInvPow J * ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) *
          P.Omega * Real.log P.OmegaOld) := by
      exact mul_le_mul_of_nonneg_left
        (BakerLemma2Concrete.initial_weightedSideLogSum_le P)
        (P.qInvPow_pos J).le

theorem norm_embedding_radicalMonomial_le_exp_heightScale
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (state : LevelState P J) (lambda : LevelIndex P J) (l : ℕ)
    (hl : l ≤ P.R (J + 1))
    (tau : SourceRadicalField P →ₐ[ℚ] ℂ) :
    ‖tau (radicalMonomial P (coordinatesForState state) lambda l)‖ ≤
      Real.exp (26 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld)) := by
  let W : ℝ :=
    (∑ r : Fin oldRank,
      ((coordinatesForState state).oldExponent lambda r : ℝ) *
        Real.log (P.oldHeight r)) +
    ((coordinatesForState state).lastExponent lambda : ℝ) *
      Real.log P.newHeight
  have hW := state_weightedExponentLogSum_le P state lambda
  have hscaled : (l : ℝ) * W ≤
      26 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) := by
    have hlR : (l : ℝ) ≤
        16 * ((P.q ^ (J + 1) : ℕ) : ℝ) * P.h := by
      exact_mod_cast hl
    have hcancel :
        P.qInvPow J * (16 * ((P.q ^ (J + 1) : ℕ) : ℝ) * P.h) =
          208 * (P.h : ℝ) := by
      unfold VDPLParameters.qInvPow
      rw [pow_succ]
      push_cast
      have hqpow : ((P.q ^ J : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast pow_ne_zero J
          (Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q))
      rw [P.q_eq]
      field_simp
      ring
    have hW0 : 0 ≤ W := by
      dsimp only [W]
      exact add_nonneg
        (Finset.sum_nonneg fun r _hr ↦
          mul_nonneg (by positivity) (P.log_oldHeight_pos r).le)
        (mul_nonneg (by positivity) P.log_newHeight_pos.le)
    have hscale0 : 0 ≤
        (1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
          Real.log P.OmegaOld := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (Real.rpow_pos_of_pos P.k_pos _).le)
          P.Omega_pos.le)
        P.log_OmegaOld_pos.le
    have hkpow : P.k ^ (1 - P.sigma) ≤ P.k := by
      calc
        P.k ^ (1 - P.sigma) ≤ P.k ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le P.one_le_k (by
            linarith [P.sigma_pos])
        _ = P.k := Real.rpow_one _
    calc
      (l : ℝ) * W ≤
          (16 * ((P.q ^ (J + 1) : ℕ) : ℝ) * P.h) *
            (P.qInvPow J * ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) *
              P.Omega * Real.log P.OmegaOld)) :=
        mul_le_mul hlR hW hW0 (by positivity)
      _ = 26 * (P.h : ℝ) *
          (P.k ^ (1 - P.sigma) * P.Omega * Real.log P.OmegaOld) := by
        rw [show
          (16 * ((P.q ^ (J + 1) : ℕ) : ℝ) * P.h) *
              (P.qInvPow J * ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) *
                P.Omega * Real.log P.OmegaOld)) =
            (P.qInvPow J * (16 * ((P.q ^ (J + 1) : ℕ) : ℝ) * P.h)) *
              ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega *
                Real.log P.OmegaOld) by ring]
        rw [hcancel]
        ring
      _ ≤ 26 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld) := by
        have htail : 0 ≤ P.Omega * Real.log P.OmegaOld :=
          mul_nonneg P.Omega_pos.le P.log_OmegaOld_pos.le
        have hp := mul_le_mul_of_nonneg_right hkpow htail
        nlinarith
  unfold radicalMonomial
  rw [map_mul, norm_mul, map_prod, norm_prod]
  calc
    (∏ r : Fin oldRank,
        ‖tau (radicalGenerator P r.castSucc ^
          ((coordinatesForState state).oldExponent lambda r * l))‖) *
        ‖tau (radicalGenerator P (Fin.last oldRank) ^
          ((coordinatesForState state).lastExponent lambda * l))‖ ≤
      (∏ r : Fin oldRank,
        P.oldHeight r ^
          ((coordinatesForState state).oldExponent lambda r * l)) *
        P.newHeight ^
          ((coordinatesForState state).lastExponent lambda * l) := by
      apply mul_le_mul
      · apply Finset.prod_le_prod
        · intro r _hr
          exact norm_nonneg _
        · intro r _hr
          rw [map_pow, norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _)
            (norm_embedding_oldRadicalGenerator_le P tau r) _
      · rw [map_pow, norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _)
          (norm_embedding_lastRadicalGenerator_le P tau) _
      · exact norm_nonneg _
      · exact Finset.prod_nonneg fun r _hr ↦
          pow_nonneg (P.oldHeight_pos r).le _
    _ = Real.exp ((l : ℝ) * W) := by
      dsimp only [W]
      calc
        (∏ r : Fin oldRank,
            P.oldHeight r ^
              ((coordinatesForState state).oldExponent lambda r * l)) *
            P.newHeight ^
              ((coordinatesForState state).lastExponent lambda * l) =
          (∏ r : Fin oldRank,
            Real.exp ((((coordinatesForState state).oldExponent lambda r * l : ℕ) : ℝ) *
              Real.log (P.oldHeight r))) *
            Real.exp ((((coordinatesForState state).lastExponent lambda * l : ℕ) : ℝ) *
              Real.log P.newHeight) := by
            congr 1
            · apply Finset.prod_congr rfl
              intro r _hr
              rw [Real.exp_nat_mul, Real.exp_log (P.oldHeight_pos r)]
            · rw [Real.exp_nat_mul, Real.exp_log P.newHeight_pos]
        _ = Real.exp
            ((∑ r : Fin oldRank,
              ((((coordinatesForState state).oldExponent lambda r * l : ℕ) : ℝ) *
                Real.log (P.oldHeight r))) +
              ((((coordinatesForState state).lastExponent lambda * l : ℕ) : ℝ) *
                Real.log P.newHeight)) := by
            rw [Real.exp_add, Real.exp_sum]
        _ = Real.exp ((l : ℝ) *
            ((∑ r : Fin oldRank,
              ((coordinatesForState state).oldExponent lambda r : ℝ) *
                Real.log (P.oldHeight r)) +
              ((coordinatesForState state).lastExponent lambda : ℝ) *
                Real.log P.newHeight)) := by
            congr 1
            push_cast
            rw [mul_add, Finset.mul_sum]
            congr 1
            · apply Finset.sum_congr rfl
              intro r _hr
              ring
            · ring
    _ ≤ Real.exp (26 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld)) := Real.exp_le_exp.mpr hscaled

/-! ## The rational common denominator -/

/-- The extra rational-grid denominator changes `J` to `J+1`; its total
loss is still strictly below four source-height exponents. -/
theorem norm_state_rational_commonDeltaDenominator_lt_exp_four_heightScale
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (hJ : P.LevelOK J)
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep J) :
    ‖(commonDeltaDenominator P.h P.LzeroPlusOne
      (P.q ^ (J + 1)) m : ℂ)‖ <
      Real.exp (4 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld)) := by
  have hqpow : 0 < P.q ^ (J + 1) :=
    pow_pos (Nat.zero_lt_of_lt P.one_lt_q) _
  refine (norm_commonDeltaDenominator_le_exp P.h P.LzeroPlusOne
    (P.q ^ (J + 1)) m hqpow).trans_lt ?_
  apply Real.exp_lt_exp.mpr
  have hm0 : m 0 ≤ P.Sstep J :=
    (VDPLMultiIndex.component_le_weight m 0).trans hm
  have hstep : (P.Sstep J : ℝ) ≤
      P.k * P.Omega * Real.log P.OmegaOld := by
    calc
      (P.Sstep J : ℝ) ≤ P.levelScale J / 9 :=
        P.Sstep_cast_le J
      _ ≤ P.k * P.Omega * Real.log P.OmegaOld := by
        have hlevel : P.levelScale J ≤
            P.k * P.Omega * Real.log P.OmegaOld := by
          unfold VDPLParameters.levelScale VDPLParameters.qInvPow
          have hinv : (((P.q ^ J : ℕ) : ℝ))⁻¹ ≤ 1 :=
            inv_le_one_of_one_le₀ (by exact_mod_cast
              (one_le_pow₀ (show 1 ≤ P.q from P.one_lt_q.le) :
                1 ≤ P.q ^ J))
          have hcore : 0 ≤ P.k * P.Omega * Real.log P.OmegaOld :=
            mul_nonneg (mul_nonneg P.k_pos.le P.Omega_pos.le)
              P.log_OmegaOld_pos.le
          simpa only [mul_assoc, one_mul] using
            mul_le_mul_of_nonneg_right hinv hcore
        have hpos : 0 ≤ P.levelScale J := (P.levelScale_pos J).le
        nlinarith
  have hL : (P.LzeroPlusOne : ℝ) ≤
      (1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega := by
    simpa only [VDPLParameters.LzeroScale] using P.LzeroPlusOne_cast_le
  have hJlog :=
    level_mul_log_q_lt_four_mul_rpow_sigma_mul_logOmegaOld P hJ
  have hlogq : Real.log (P.q : ℝ) <
      P.k ^ P.sigma * Real.log P.OmegaOld := by
    have hK : (128 : ℝ) <
        P.k ^ P.sigma * Real.log P.OmegaOld := by
      have hk := BakerLemma2Concrete.twoHundredFiftySix_le_k_rpow_sigma P
      have hL : (1 / 2 : ℝ) < Real.log P.OmegaOld := by
        nlinarith [Real.log_two_gt_d9, P.log_two_le_log_OmegaOld]
      calc
        (128 : ℝ) = 256 * (1 / 2 : ℝ) := by norm_num
        _ ≤ P.k ^ P.sigma * (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hk (by norm_num)
        _ < P.k ^ P.sigma * Real.log P.OmegaOld :=
          mul_lt_mul_of_pos_left hL (Real.rpow_pos_of_pos P.k_pos _)
    have hlog13 : Real.log (P.q : ℝ) ≤ 12 := by
      rw [P.q_eq]
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 13)
      norm_num at h ⊢
      exact h
    linarith
  have hsuccLog : ((J + 1 : ℕ) : ℝ) * Real.log P.q <
      5 * P.k ^ P.sigma * Real.log P.OmegaOld := by
    push_cast
    nlinarith
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    rw [Real.log_four_eq]
    nlinarith [Real.log_two_lt_d9]
  have hhead :
      (2 * (P.h : ℝ) * P.LzeroPlusOne) *
          (((J + 1 : ℕ) : ℝ) * Real.log P.q) <
        (5 / 4 : ℝ) * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld) := by
    have hleft : 0 ≤ 2 * (P.h : ℝ) := by positivity
    have hlog0 : 0 ≤ ((J + 1 : ℕ) : ℝ) * Real.log P.q :=
      mul_nonneg (by positivity) (Real.log_nonneg (by
        exact_mod_cast P.one_lt_q.le))
    have hcoef : 0 < 2 * (P.h : ℝ) *
        ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega) := by
      exact mul_pos
        (mul_pos (by norm_num) (by exact_mod_cast P.h_pos))
        (mul_pos
          (mul_pos (by norm_num) (Real.rpow_pos_of_pos P.k_pos _))
          P.Omega_pos)
    calc
      (2 * (P.h : ℝ) * P.LzeroPlusOne) *
          (((J + 1 : ℕ) : ℝ) * Real.log P.q) ≤
        (2 * (P.h : ℝ) *
          ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega)) *
            (((J + 1 : ℕ) : ℝ) * Real.log P.q) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL hleft) hlog0
      _ < (2 * (P.h : ℝ) *
          ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega)) *
            (5 * P.k ^ P.sigma * Real.log P.OmegaOld) :=
        mul_lt_mul_of_pos_left hsuccLog hcoef
      _ = (5 / 4 : ℝ) * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld) := by
        calc
          (2 * (P.h : ℝ) *
              ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega)) *
                (5 * P.k ^ P.sigma * Real.log P.OmegaOld) =
              (5 / 4 : ℝ) * (P.h : ℝ) * P.Omega *
                Real.log P.OmegaOld *
                  (P.k ^ (1 - P.sigma) * P.k ^ P.sigma) := by ring
          _ = (5 / 4 : ℝ) * ((P.h : ℝ) * P.k * P.Omega *
                Real.log P.OmegaOld) := by
            rw [BakerLemma2Concrete.k_rpow_one_sub_sigma_mul_rpow_sigma P]
            ring
  have hlcm : ((P.h : ℝ) * m 0) * Real.log 4 ≤
      2 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld) := by
    have hm0r : (m 0 : ℝ) ≤ P.Sstep J := by exact_mod_cast hm0
    have hmB : (P.h : ℝ) * (m 0 : ℝ) ≤
        (P.h : ℝ) * (P.k * P.Omega * Real.log P.OmegaOld) :=
      mul_le_mul_of_nonneg_left (hm0r.trans hstep) (by positivity)
    calc
      ((P.h : ℝ) * (m 0 : ℝ)) * Real.log 4 ≤
          ((P.h : ℝ) * (P.k * P.Omega * Real.log P.OmegaOld)) *
            Real.log 4 :=
        mul_le_mul_of_nonneg_right hmB (Real.log_nonneg (by norm_num))
      _ ≤ ((P.h : ℝ) *
            (P.k * P.Omega * Real.log P.OmegaOld)) * 2 :=
        mul_le_mul_of_nonneg_left hlog4
          (mul_nonneg (by positivity)
            (mul_nonneg (mul_nonneg P.k_pos.le P.Omega_pos.le)
              P.log_OmegaOld_pos.le))
      _ = 2 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld) := by ring
  rw [show Real.log ((P.q ^ (J + 1) : ℕ) : ℝ) =
      (((J + 1 : ℕ) : ℝ)) * Real.log P.q by
    push_cast
    rw [Real.log_pow]
    simp only [Nat.cast_add, Nat.cast_one]]
  push_cast at hhead hlcm ⊢
  have hHpos :
      0 < (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld := by
    exact mul_pos
      (mul_pos (mul_pos (by exact_mod_cast P.h_pos) P.k_pos) P.Omega_pos)
      P.log_OmegaOld_pos
  linarith

/-- The exponential majorant in every nonzero concrete state is at least
one. -/
theorem one_le_stateExponentialMajorant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (z : ℂ)
    (m : VDPLMultiIndex (oldRank + 1)) :
    1 ≤ (stateSourceMajorants P state b bLast z m).exponentialMajorant := by
  obtain ⟨lambda, hlambda⟩ := state.exists_coeff_ne_zero
  unfold stateSourceMajorants exactSourceMajorants
  dsimp only
  calc
    (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp
        (‖modifiedRate (coordinatesForState state) b bLast (oldLog P) lambda‖ *
          ‖z‖) := Real.exp_le_exp.mpr (by positivity)
    _ ≤ ∑ lambda' ∈ state.support,
        Real.exp
          (‖modifiedRate (coordinatesForState state) b bLast (oldLog P)
            lambda'‖ * ‖z‖) := by
      let f := fun lambda' : LevelIndex P J ↦
        Real.exp
          (‖modifiedRate (coordinatesForState state) b bLast (oldLog P)
            lambda'‖ * ‖z‖)
      change f lambda ≤ ∑ lambda' ∈ state.support, f lambda'
      exact Finset.single_le_sum
        (f := f) (a := lambda)
        (fun i _hi ↦ (Real.exp_pos _).le) (state.mem_support lambda)

/-- A rational target term under an arbitrary embedding is controlled by
the canonical Delta majorant and the uniform radical-monomial bound. -/
theorem norm_embedding_rationalTargetTerm_le {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (hl : l ≤ P.R (J + 1)) (m : VDPLMultiIndex (oldRank + 1))
    (lambda : LevelIndex P J)
    (tau : SourceRadicalField P →ₐ[ℚ] ℂ) :
    ‖tau (rationalTargetTerm P (coordinatesForState state) P.h b bLast J
      lambda l m)‖ ≤
      (stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ)) m).deltaMajorant *
        Real.exp (26 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld)) := by
  let x : ℚ := (l : ℚ) / P.q ^ (J + 1)
  have hq : P.q ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q)
  have hx : (x : ℂ) =
      scaledArgument P.q J ((l : ℂ) / (P.q : ℂ)) := by
    dsimp only [x]
    exact (scaledArgument_div_q_eq_ratCast hq).symm
  have haux :
      ‖tau (algebraMap ℚ (SourceRadicalField P)
        (rationalAuxiliaryFactor (coordinatesForState state) P.h b bLast
          lambda x m))‖ =
      ‖auxiliaryFactor (coordinatesForState state) P.h b bLast lambda
        (scaledArgument P.q J ((l : ℂ) / (P.q : ℂ))) m‖ := by
    rw [tau.commutes]
    change ‖(rationalAuxiliaryFactor (coordinatesForState state) P.h b
      bLast lambda x m : ℂ)‖ = _
    rw [coe_rationalAuxiliaryFactor]
    rw [hx]
  unfold rationalTargetTerm
  change ‖tau (algebraMap ℚ (SourceRadicalField P)
      (rationalAuxiliaryFactor (coordinatesForState state) P.h b bLast
        lambda x m) *
    radicalMonomial P (coordinatesForState state) lambda l)‖ ≤ _
  rw [map_mul, norm_mul, haux]
  exact mul_le_mul
    ((stateSourceMajorants P state b bLast ((l : ℂ) / (P.q : ℂ)) m).delta_le
      lambda (state.mem_support lambda))
    (norm_embedding_radicalMonomial_le_exp_heightScale
      P state lambda l hl tau)
    (norm_nonneg _)
    (stateSourceMajorants P state b bLast
      ((l : ℂ) / (P.q : ℂ)) m).deltaMajorant_nonneg

/-- A single conjugate of the completely cleared algebraic auxiliary value
is bounded by the common denominator, the ordinary source growth majorant,
and the radical loss `exp(26H)`. -/
theorem norm_embedding_cleared_rationalAuxiliaryValue_le {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (hl : l ≤ P.R (J + 1)) (m : VDPLMultiIndex (oldRank + 1))
    (tau : SourceRadicalField P →ₐ[ℚ] ℂ) :
    ‖tau
      (algebraMap ℚ (SourceRadicalField P)
          (commonDeltaDenominator P.h P.LzeroPlusOne
            (P.q ^ (J + 1)) m) *
        algebraicAuxiliaryValue state.support state.coeff
          (fun lambda ↦ rationalTargetTerm P (coordinatesForState state)
            P.h b bLast J lambda l m))‖ ≤
      ‖(commonDeltaDenominator P.h P.LzeroPlusOne
          (P.q ^ (J + 1)) m : ℂ)‖ *
        (stateSourceMajorants P state b bLast
          ((l : ℂ) / (P.q : ℂ)) m).growth *
        Real.exp (26 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld)) := by
  let M := stateSourceMajorants P state b bLast
    ((l : ℂ) / (P.q : ℂ)) m
  let D : ℝ := ‖(commonDeltaDenominator P.h P.LzeroPlusOne
    (P.q ^ (J + 1)) m : ℂ)‖
  let R : ℝ := Real.exp (26 * ((P.h : ℝ) * P.k * P.Omega *
    Real.log P.OmegaOld))
  have hterm : ∀ lambda ∈ state.support,
      ‖tau ((state.coeff lambda : SourceRadicalField P) *
        rationalTargetTerm P (coordinatesForState state) P.h b bLast J
          lambda l m)‖ ≤ P.coeffHeight * M.deltaMajorant * R := by
    intro lambda hlambda
    rw [map_mul, norm_mul]
    have hcoeff : ‖tau (state.coeff lambda : SourceRadicalField P)‖ ≤
        P.coeffHeight := by
      simpa only [map_intCast, Complex.norm_intCast, Real.norm_eq_abs] using
        state.coeff_height lambda
    have htarget :=
      norm_embedding_rationalTargetTerm_le P state b bLast l hl m lambda tau
    calc
      ‖tau (state.coeff lambda : SourceRadicalField P)‖ *
          ‖tau (rationalTargetTerm P (coordinatesForState state) P.h b
            bLast J lambda l m)‖ ≤
        P.coeffHeight * (M.deltaMajorant * R) :=
          mul_le_mul hcoeff (by simpa only [M, R] using htarget)
            (norm_nonneg _) P.coeffHeight_pos.le
      _ = P.coeffHeight * M.deltaMajorant * R := by ring
  have hsum :
      ‖tau (algebraicAuxiliaryValue state.support state.coeff
        (fun lambda ↦ rationalTargetTerm P (coordinatesForState state)
          P.h b bLast J lambda l m))‖ ≤
        (state.support.card : ℝ) * (P.coeffHeight * M.deltaMajorant * R) := by
    unfold algebraicAuxiliaryValue
    rw [map_sum]
    refine (norm_sum_le _ _).trans ?_
    calc
      ∑ lambda ∈ state.support,
          ‖tau ((state.coeff lambda : SourceRadicalField P) *
            rationalTargetTerm P (coordinatesForState state) P.h b bLast J
              lambda l m)‖ ≤
        ∑ _lambda ∈ state.support,
          (P.coeffHeight * M.deltaMajorant * R) :=
            Finset.sum_le_sum fun lambda hlambda ↦ hterm lambda hlambda
      _ = (state.support.card : ℝ) *
          (P.coeffHeight * M.deltaMajorant * R) := by simp
  have hbaseNonneg : 0 ≤
      (state.support.card : ℝ) * (P.coeffHeight * M.deltaMajorant) := by
    exact mul_nonneg (by positivity)
      (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg)
  have hbaseGrowth :
      (state.support.card : ℝ) * (P.coeffHeight * M.deltaMajorant) ≤
        M.growth := by
    unfold BakerLemma3Concrete.SourceMajorants.growth
    dsimp only [M, stateSourceMajorants, exactSourceMajorants]
    exact le_mul_of_one_le_right hbaseNonneg
      (one_le_stateExponentialMajorant P state b bLast
        ((l : ℂ) / (P.q : ℂ)) m)
  have hsum' :
      ‖tau (algebraicAuxiliaryValue state.support state.coeff
        (fun lambda ↦ rationalTargetTerm P (coordinatesForState state)
          P.h b bLast J lambda l m))‖ ≤ M.growth * R := by
    calc
      _ ≤ (state.support.card : ℝ) *
          (P.coeffHeight * M.deltaMajorant * R) := hsum
      _ = ((state.support.card : ℝ) *
          (P.coeffHeight * M.deltaMajorant)) * R := by ring
      _ ≤ M.growth * R :=
        mul_le_mul_of_nonneg_right hbaseGrowth (by positivity)
  rw [map_mul, norm_mul]
  have hDmap :
      ‖tau (algebraMap ℚ (SourceRadicalField P)
        (commonDeltaDenominator P.h P.LzeroPlusOne
          (P.q ^ (J + 1)) m))‖ = D := by
    dsimp only [D]
    rw [tau.commutes]
    rfl
  rw [hDmap]
  simpa only [M, R, mul_assoc] using
    mul_le_mul_of_nonneg_left hsum' (norm_nonneg _)

/-- The automatic conjugate bound is controlled by the number-field degree
times the preceding uniform bound. -/
theorem rationalTargetConjugateBound_le {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (hl : l ≤ P.R (J + 1)) (m : VDPLMultiIndex (oldRank + 1)) :
    rationalTargetConjugateBound P (coordinatesForState state)
        state.support state.coeff P.h P.LzeroPlusOne b bLast J l m ≤
      1 + (13 ^ (oldRank + 1) : ℝ) *
        ‖(commonDeltaDenominator P.h P.LzeroPlusOne
          (P.q ^ (J + 1)) m : ℂ)‖ *
        (stateSourceMajorants P state b bLast
          ((l : ℂ) / (P.q : ℂ)) m).growth *
        Real.exp (26 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld)) := by
  unfold rationalTargetConjugateBound
  gcongr
  calc
    ∑ tau : SourceRadicalField P →ₐ[ℚ] ℂ,
        ‖tau
          (algebraMap ℚ (SourceRadicalField P)
              (commonDeltaDenominator P.h P.LzeroPlusOne
                (P.q ^ (J + 1)) m) *
            algebraicAuxiliaryValue state.support state.coeff
              (fun lambda ↦ rationalTargetTerm P (coordinatesForState state)
                P.h b bLast J lambda l m))‖ ≤
      ∑ _tau : SourceRadicalField P →ₐ[ℚ] ℂ,
        (‖(commonDeltaDenominator P.h P.LzeroPlusOne
            (P.q ^ (J + 1)) m : ℂ)‖ *
          (stateSourceMajorants P state b bLast
            ((l : ℂ) / (P.q : ℂ)) m).growth *
          Real.exp (26 * ((P.h : ℝ) * P.k * P.Omega *
            Real.log P.OmegaOld))) :=
      Finset.sum_le_sum fun tau _htau ↦
        norm_embedding_cleared_rationalAuxiliaryValue_le
          P state b bLast l hl m tau
    _ = (13 ^ (oldRank + 1) : ℝ) *
        ‖(commonDeltaDenominator P.h P.LzeroPlusOne
          (P.q ^ (J + 1)) m : ℂ)‖ *
        (stateSourceMajorants P state b bLast
          ((l : ℂ) / (P.q : ℂ)) m).growth *
        Real.exp (26 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, AlgHom.card,
        finrank_sourceRadicalField]
      push_cast
      ring

/-! ## Source-faithful conjugate bound -/

/-- A conjugate of the cleared rational value is controlled by the
level-scaled algebraic growth.  Unlike the ordinary `SourceMajorants.growth`,
this quantity retains the cancelling factor `q ^ (-J)` in every algebraic
exponential rate. -/
theorem norm_embedding_cleared_rationalAuxiliaryValue_le_levelAlgebraicGrowth
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (hl : l ≤ P.R (J + 1)) (m : VDPLMultiIndex (oldRank + 1))
    (tau : SourceRadicalField P →ₐ[ℚ] ℂ) :
    ‖tau
      (algebraMap ℚ (SourceRadicalField P)
          (commonDeltaDenominator P.h P.LzeroPlusOne
            (P.q ^ (J + 1)) m) *
        algebraicAuxiliaryValue state.support state.coeff
          (fun lambda ↦ rationalTargetTerm P (coordinatesForState state)
            P.h b bLast J lambda l m))‖ ≤
      ‖(commonDeltaDenominator P.h P.LzeroPlusOne
          (P.q ^ (J + 1)) m : ℂ)‖ *
        (levelAlgebraicExponentialMajorant P state b bLast
          ((l : ℂ) / (P.q : ℂ)) m).growth *
        Real.exp (26 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld)) := by
  let M := stateSourceMajorants P state b bLast
    ((l : ℂ) / (P.q : ℂ)) m
  let A := levelAlgebraicExponentialMajorant P state b bLast
    ((l : ℂ) / (P.q : ℂ)) m
  let D : ℝ := ‖(commonDeltaDenominator P.h P.LzeroPlusOne
    (P.q ^ (J + 1)) m : ℂ)‖
  let R : ℝ := Real.exp (26 * ((P.h : ℝ) * P.k * P.Omega *
    Real.log P.OmegaOld))
  have hterm : ∀ lambda ∈ state.support,
      ‖tau ((state.coeff lambda : SourceRadicalField P) *
        rationalTargetTerm P (coordinatesForState state) P.h b bLast J
          lambda l m)‖ ≤ P.coeffHeight * M.deltaMajorant * R := by
    intro lambda hlambda
    rw [map_mul, norm_mul]
    have hcoeff : ‖tau (state.coeff lambda : SourceRadicalField P)‖ ≤
        P.coeffHeight := by
      simpa only [map_intCast, Complex.norm_intCast, Real.norm_eq_abs] using
        state.coeff_height lambda
    have htarget :=
      norm_embedding_rationalTargetTerm_le P state b bLast l hl m lambda tau
    calc
      ‖tau (state.coeff lambda : SourceRadicalField P)‖ *
          ‖tau (rationalTargetTerm P (coordinatesForState state) P.h b
            bLast J lambda l m)‖ ≤
        P.coeffHeight * (M.deltaMajorant * R) :=
          mul_le_mul hcoeff (by simpa only [M, R] using htarget)
            (norm_nonneg _) P.coeffHeight_pos.le
      _ = P.coeffHeight * M.deltaMajorant * R := by ring
  have hsum :
      ‖tau (algebraicAuxiliaryValue state.support state.coeff
        (fun lambda ↦ rationalTargetTerm P (coordinatesForState state)
          P.h b bLast J lambda l m))‖ ≤
        (state.support.card : ℝ) * (P.coeffHeight * M.deltaMajorant * R) := by
    unfold algebraicAuxiliaryValue
    rw [map_sum]
    refine (norm_sum_le _ _).trans ?_
    calc
      ∑ lambda ∈ state.support,
          ‖tau ((state.coeff lambda : SourceRadicalField P) *
            rationalTargetTerm P (coordinatesForState state) P.h b bLast J
              lambda l m)‖ ≤
        ∑ _lambda ∈ state.support,
          (P.coeffHeight * M.deltaMajorant * R) :=
            Finset.sum_le_sum fun lambda hlambda ↦ hterm lambda hlambda
      _ = (state.support.card : ℝ) *
          (P.coeffHeight * M.deltaMajorant * R) := by simp
  have hbaseNonneg : 0 ≤
      (state.support.card : ℝ) * (P.coeffHeight * M.deltaMajorant) := by
    exact mul_nonneg (by positivity)
      (mul_nonneg P.coeffHeight_pos.le M.deltaMajorant_nonneg)
  have hrateNonneg : 0 ≤
      P.qInvPow J * sourceAlgebraicRateBound P *
        ‖((l : ℂ) / (P.q : ℂ))‖ := by
    exact mul_nonneg
      (mul_nonneg (P.qInvPow_pos J).le
        (sourceAlgebraicRateBound_nonneg P))
      (norm_nonneg _)
  have hbaseGrowth :
      (state.support.card : ℝ) * (P.coeffHeight * M.deltaMajorant) ≤
        A.growth := by
    unfold BakerSourceAlgebraicMajorant.AlgebraicExponentialMajorant.growth
    change
      (state.support.card : ℝ) * (P.coeffHeight * M.deltaMajorant) ≤
        (state.support.card : ℝ) * (P.coeffHeight * M.deltaMajorant) *
          Real.exp (P.qInvPow J * sourceAlgebraicRateBound P *
            ‖((l : ℂ) / (P.q : ℂ))‖)
    exact le_mul_of_one_le_right hbaseNonneg (Real.one_le_exp hrateNonneg)
  have hsum' :
      ‖tau (algebraicAuxiliaryValue state.support state.coeff
        (fun lambda ↦ rationalTargetTerm P (coordinatesForState state)
          P.h b bLast J lambda l m))‖ ≤ A.growth * R := by
    calc
      _ ≤ (state.support.card : ℝ) *
          (P.coeffHeight * M.deltaMajorant * R) := hsum
      _ = ((state.support.card : ℝ) *
          (P.coeffHeight * M.deltaMajorant)) * R := by ring
      _ ≤ A.growth * R :=
        mul_le_mul_of_nonneg_right hbaseGrowth (by positivity)
  rw [map_mul, norm_mul]
  have hDmap :
      ‖tau (algebraMap ℚ (SourceRadicalField P)
        (commonDeltaDenominator P.h P.LzeroPlusOne
          (P.q ^ (J + 1)) m))‖ = D := by
    dsimp only [D]
    rw [tau.commutes]
    rfl
  rw [hDmap]
  simpa only [A, R, mul_assoc] using
    mul_le_mul_of_nonneg_left hsum' (norm_nonneg _)

/-- The complete conjugate sum is bounded using the level-scaled algebraic
growth, so no ratio between logarithmic-form coefficients appears. -/
theorem rationalTargetConjugateBound_le_levelAlgebraicGrowth
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ) (l : ℕ)
    (hl : l ≤ P.R (J + 1)) (m : VDPLMultiIndex (oldRank + 1)) :
    rationalTargetConjugateBound P (coordinatesForState state)
        state.support state.coeff P.h P.LzeroPlusOne b bLast J l m ≤
      1 + (13 ^ (oldRank + 1) : ℝ) *
        ‖(commonDeltaDenominator P.h P.LzeroPlusOne
          (P.q ^ (J + 1)) m : ℂ)‖ *
        (levelAlgebraicExponentialMajorant P state b bLast
          ((l : ℂ) / (P.q : ℂ)) m).growth *
        Real.exp (26 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld)) := by
  unfold rationalTargetConjugateBound
  gcongr
  calc
    ∑ tau : SourceRadicalField P →ₐ[ℚ] ℂ,
        ‖tau
          (algebraMap ℚ (SourceRadicalField P)
              (commonDeltaDenominator P.h P.LzeroPlusOne
                (P.q ^ (J + 1)) m) *
            algebraicAuxiliaryValue state.support state.coeff
              (fun lambda ↦ rationalTargetTerm P (coordinatesForState state)
                P.h b bLast J lambda l m))‖ ≤
      ∑ _tau : SourceRadicalField P →ₐ[ℚ] ℂ,
        (‖(commonDeltaDenominator P.h P.LzeroPlusOne
            (P.q ^ (J + 1)) m : ℂ)‖ *
          (levelAlgebraicExponentialMajorant P state b bLast
            ((l : ℂ) / (P.q : ℂ)) m).growth *
          Real.exp (26 * ((P.h : ℝ) * P.k * P.Omega *
            Real.log P.OmegaOld))) :=
      Finset.sum_le_sum fun tau _htau ↦
        norm_embedding_cleared_rationalAuxiliaryValue_le_levelAlgebraicGrowth
          P state b bLast l hl m tau
    _ = (13 ^ (oldRank + 1) : ℝ) *
        ‖(commonDeltaDenominator P.h P.LzeroPlusOne
          (P.q ^ (J + 1)) m : ℂ)‖ *
        (levelAlgebraicExponentialMajorant P state b bLast
          ((l : ℂ) / (P.q : ℂ)) m).growth *
        Real.exp (26 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, AlgHom.card,
        finrank_sourceRadicalField]
      push_cast
      ring

/-! ## Closing the rational Liouville product -/

/-- The radical-field degree factor `q^rank` is at most the source's
`k^(mu/2)` reserve. -/
theorem sourceDegree_le_k_rpow_mu_div_two {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    (13 ^ (oldRank + 1) : ℝ) ≤ P.k ^ (P.mu / 2) := by
  have hbase := P.q_le_k_rpow_mu_div_two_rank_add_one
  have hpow : (P.q : ℝ) ^ P.rank ≤
      (P.k ^ (P.mu / (2 * (P.rank + 1 : ℝ)))) ^ P.rank :=
    pow_le_pow_left₀ (by positivity) hbase P.rank
  calc
    (13 ^ (oldRank + 1) : ℝ) = (P.q : ℝ) ^ P.rank := by
      norm_num [P.q_eq, VDPLParameters.rank]
    _ ≤ (P.k ^ (P.mu / (2 * (P.rank + 1 : ℝ)))) ^ P.rank := hpow
    _ = P.k ^
        ((P.mu / (2 * (P.rank + 1 : ℝ))) * P.rank) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul P.k_pos.le]
    _ ≤ P.k ^ (P.mu / 2) := by
      apply Real.rpow_le_rpow_of_exponent_le P.one_le_k
      have hr : (0 : ℝ) < P.rank + 1 := by positivity
      have hrank : (0 : ℝ) ≤ P.rank := by positivity
      rw [P.mu_eq]
      field_simp
      nlinarith

/-- The structural quarter-scale source exponent is bounded by `kH`, where
`H=h*k*Omega*log OmegaOld`. -/
theorem sourceExponent_structural_quarter_le_k_mul_heightScale
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) :
    sourceExponent P (P.C * Real.log P.OmegaOld) / 4 ≤
      P.k * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld) := by
  have hlogB : Real.log P.Bsrc ≤ 2 * (P.h : ℝ) := by
    have h := P.log_Bsrc_lt_h_add_one
    have hh : (1 : ℝ) ≤ P.h := by exact_mod_cast P.one_le_h
    linarith
  have hC : P.C = P.k ^ 2 := by
    unfold VDPLParameters.C
    rw [P.mu_eq]
    norm_num [Real.rpow_two]
  unfold sourceExponent VDPLParameters.Omega
  rw [hC]
  have hcore : 0 ≤ P.k ^ 2 * Real.log P.OmegaOld * P.OmegaOld *
      Real.log P.newHeight := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (sq_nonneg P.k) P.log_OmegaOld_pos.le)
        P.OmegaOld_pos.le)
      P.log_newHeight_pos.le
  have hmul := mul_le_mul_of_nonneg_left hlogB hcore
  calc
    (P.k ^ 2 * Real.log P.OmegaOld) * P.OmegaOld *
          Real.log P.newHeight * Real.log P.Bsrc / 4 ≤
        (P.k ^ 2 * Real.log P.OmegaOld) * P.OmegaOld *
          Real.log P.newHeight * (2 * P.h) / 4 := by nlinarith
    _ = (1 / 2 : ℝ) * (P.k * ((P.h : ℝ) * P.k *
          (P.OmegaOld * Real.log P.newHeight) *
            Real.log P.OmegaOld)) := by ring
    _ ≤ P.k * ((P.h : ℝ) * P.k *
          (P.OmegaOld * Real.log P.newHeight) *
            Real.log P.OmegaOld) := by
      have hnonneg : 0 ≤ P.k * ((P.h : ℝ) * P.k *
          (P.OmegaOld * Real.log P.newHeight) *
            Real.log P.OmegaOld) := by
        exact mul_nonneg P.k_pos.le
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity) P.k_pos.le)
              (mul_nonneg P.OmegaOld_pos.le P.log_newHeight_pos.le))
            P.log_OmegaOld_pos.le)
      nlinarith

/-- Standard height scale used in the rational conjugate estimates. -/
def rationalHeightScale {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℝ :=
  (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld

theorem one_le_rationalHeightScale {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    1 ≤ rationalHeightScale P := by
  have hscale := BakerLemma2Concrete.six_lt_initial_levelScale P
  rw [BakerLemma2Concrete.initial_levelScale_formula] at hscale
  unfold rationalHeightScale
  have hh : (1 : ℝ) ≤ P.h := by exact_mod_cast P.one_le_h
  have hbase0 : 0 ≤ P.k * P.Omega * Real.log P.OmegaOld :=
    mul_nonneg (mul_nonneg P.k_pos.le P.Omega_pos.le)
      P.log_OmegaOld_pos.le
  have hmul := mul_le_mul_of_nonneg_right hh hbase0
  nlinarith

theorem k_le_rationalHeightScale {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    P.k ≤ rationalHeightScale P := by
  unfold rationalHeightScale
  have hfactor : (1 : ℝ) ≤
      (P.h : ℝ) * P.Omega * Real.log P.OmegaOld := by
    have hh : (2 : ℝ) ≤ P.h := by exact_mod_cast P.two_le_h
    have hO : (1 : ℝ) ≤ P.Omega := P.one_le_Omega
    have hL : (1 / 2 : ℝ) < Real.log P.OmegaOld := by
      nlinarith [Real.log_two_gt_d9, P.log_two_le_log_OmegaOld]
    nlinarith [mul_le_mul hh hO (by norm_num) (by positivity)]
  have hk : 0 ≤ P.k := P.k_pos.le
  nlinarith [mul_le_mul_of_nonneg_left hfactor hk]

/-- Fixed-family coefficient absorbing the full rational Liouville product. -/
def rationalLiouvilleAbsorptionConstant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℝ :=
  5 + P.k ^ (P.mu / 2) * (P.k + 32)

theorem rationalLiouvilleAbsorptionConstant_pos {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    0 < rationalLiouvilleAbsorptionConstant P := by
  unfold rationalLiouvilleAbsorptionConstant
  have hkpow : 0 ≤ P.k ^ (P.mu / 2) :=
    (Real.rpow_pos_of_pos P.k_pos _).le
  nlinarith [P.k_pos]

/-- On the full Lemma-5 grid, the exact product occurring in the rational
Liouville threshold is bounded by one fixed-family multiple of `H`. -/
theorem rationalLiouvilleProduct_le_exp_absorption
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (hJ : P.LevelOK J)
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (l : ℕ) (hl : l ≤ P.R (J + 1))
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep J)
    (hgrowth :
      (stateSourceMajorants P state b bLast
        ((l : ℂ) / (P.q : ℂ)) m).growth ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4)) :
    2 *
        (rationalTargetConjugateBound P (coordinatesForState state)
            state.support state.coeff P.h P.LzeroPlusOne b bLast J l m ^
          (13 ^ (oldRank + 1) - 1)) *
        ‖(commonDeltaDenominator P.h P.LzeroPlusOne
          (P.q ^ (J + 1)) m : ℂ)‖ ≤
      Real.exp (rationalLiouvilleAbsorptionConstant P *
        rationalHeightScale P) := by
  let X := rationalHeightScale P
  let d : ℕ := 13 ^ (oldRank + 1)
  let D : ℝ := ‖(commonDeltaDenominator P.h P.LzeroPlusOne
    (P.q ^ (J + 1)) m : ℂ)‖
  let G : ℝ := (stateSourceMajorants P state b bLast
    ((l : ℂ) / (P.q : ℂ)) m).growth
  let T : ℝ := rationalTargetConjugateBound P (coordinatesForState state)
    state.support state.coeff P.h P.LzeroPlusOne b bLast J l m
  have hX : 1 ≤ X := one_le_rationalHeightScale P
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hkX : P.k ≤ X := k_le_rationalHeightScale P
  have hD : D < Real.exp (4 * X) := by
    simpa only [D, X, rationalHeightScale] using
      norm_state_rational_commonDeltaDenominator_lt_exp_four_heightScale
        P hJ m hm
  have hDle : D ≤ Real.exp (4 * X) := hD.le
  have hG : G ≤ Real.exp (P.k * X) := by
    refine hgrowth.trans (Real.exp_le_exp.mpr ?_)
    simpa only [X, rationalHeightScale] using
      sourceExponent_structural_quarter_le_k_mul_heightScale P
  have hdK : (d : ℝ) ≤ P.k ^ (P.mu / 2) := by
    simpa only [d, Nat.cast_pow, Nat.cast_ofNat] using
      sourceDegree_le_k_rpow_mu_div_two P
  have hkpowk : P.k ^ (P.mu / 2) ≤ P.k := by
    calc
      P.k ^ (P.mu / 2) ≤ P.k ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le P.one_le_k (by
          rw [P.mu_eq]
          norm_num)
      _ = P.k := Real.rpow_one _
  have hdX : (d : ℝ) ≤ X := hdK.trans (hkpowk.trans hkX)
  have hdexp : (d : ℝ) ≤ Real.exp X := by
    exact hdX.trans (by nlinarith [Real.add_one_le_exp X])
  have hTraw := rationalTargetConjugateBound_le
    P state b bLast l hl m
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    unfold BakerLemma3Concrete.SourceMajorants.growth
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg P.coeffHeight_pos.le
          (stateSourceMajorants P state b bLast
            ((l : ℂ) / (P.q : ℂ)) m).deltaMajorant_nonneg))
      (stateSourceMajorants P state b bLast
        ((l : ℂ) / (P.q : ℂ)) m).exponentialMajorant_nonneg
  have hT : T ≤ Real.exp ((P.k + 32) * X) := by
    have hproduct :
        (d : ℝ) * D * G * Real.exp (26 * X) ≤
          Real.exp ((P.k + 31) * X) := by
      calc
        (d : ℝ) * D * G * Real.exp (26 * X) ≤
            Real.exp X * Real.exp (4 * X) * Real.exp (P.k * X) *
              Real.exp (26 * X) := by
          have h1 : (d : ℝ) * D ≤
              Real.exp X * Real.exp (4 * X) :=
            mul_le_mul hdexp hDle (norm_nonneg _) (Real.exp_pos _).le
          have h2 : (d : ℝ) * D * G ≤
              Real.exp X * Real.exp (4 * X) * Real.exp (P.k * X) :=
            mul_le_mul h1 hG hG0 (by positivity)
          exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = Real.exp ((P.k + 31) * X) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
    have hone : (1 : ℝ) ≤ Real.exp ((P.k + 31) * X) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hk : 0 ≤ P.k + 31 := by linarith [P.k_pos]
      positivity
    have htwo : (2 : ℝ) ≤ Real.exp X := by
      nlinarith [Real.exp_one_gt_two.le,
        Real.exp_le_exp.mpr hX]
    calc
      T ≤ 1 + (d : ℝ) * D * G * Real.exp (26 * X) := by
        simpa only [T, d, D, G, X, rationalHeightScale, Nat.cast_pow,
          Nat.cast_ofNat] using hTraw
      _ ≤ 2 * Real.exp ((P.k + 31) * X) := by linarith
      _ ≤ Real.exp X * Real.exp ((P.k + 31) * X) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp ((P.k + 32) * X) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hTpow : T ^ (d - 1) ≤
      Real.exp ((P.k ^ (P.mu / 2) * (P.k + 32)) * X) := by
    calc
      T ^ (d - 1) ≤ (Real.exp ((P.k + 32) * X)) ^ (d - 1) := by
        exact pow_le_pow_left₀ (by
          exact (rationalTargetConjugateBound_pos P
            (coordinatesForState state) state.support state.coeff P.h
            P.LzeroPlusOne b bLast J l m).le) hT _
      _ = Real.exp (((d - 1 : ℕ) : ℝ) * ((P.k + 32) * X)) := by
        rw [Real.exp_nat_mul]
      _ ≤ Real.exp ((P.k ^ (P.mu / 2) * (P.k + 32)) * X) := by
        apply Real.exp_le_exp.mpr
        have hdsub : ((d - 1 : ℕ) : ℝ) ≤ P.k ^ (P.mu / 2) := by
          have hcast : ((d - 1 : ℕ) : ℝ) ≤ (d : ℝ) := by
            exact_mod_cast Nat.sub_le d 1
          exact hcast.trans hdK
        have hright : 0 ≤ (P.k + 32) * X :=
          mul_nonneg (by linarith [P.k_pos]) hX0
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hdsub hright
  have htwo : (2 : ℝ) ≤ Real.exp X := by
    nlinarith [Real.exp_one_gt_two.le, Real.exp_le_exp.mpr hX]
  calc
    2 * T ^ (d - 1) * D ≤
        Real.exp X *
          Real.exp ((P.k ^ (P.mu / 2) * (P.k + 32)) * X) *
            Real.exp (4 * X) := by
      have hTpow0 : 0 ≤ T ^ (d - 1) := pow_nonneg (by
        exact (rationalTargetConjugateBound_pos P
          (coordinatesForState state) state.support state.coeff P.h
          P.LzeroPlusOne b bLast J l m).le) _
      have hmul : 2 * T ^ (d - 1) ≤
          Real.exp X *
            Real.exp ((P.k ^ (P.mu / 2) * (P.k + 32)) * X) :=
        mul_le_mul htwo hTpow hTpow0 (Real.exp_pos _).le
      exact mul_le_mul hmul hDle (norm_nonneg _) (by positivity)
    _ = Real.exp (rationalLiouvilleAbsorptionConstant P * X) := by
      rw [← Real.exp_add, ← Real.exp_add]
      unfold rationalLiouvilleAbsorptionConstant
      congr 1
      ring

/-- Enlarging the normalized constant absorbs the exact rational Liouville
product into `exp(3E/4)`, uniformly over the complete Lemma-5 grid. -/
theorem rationalLiouvilleProduct_le_exp_three_quarters
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (hJ : P.LevelOK J)
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (l : ℕ) (hl : l ≤ P.R (J + 1))
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep J)
    (C₀ : ℝ)
    (hC : 4 * rationalLiouvilleAbsorptionConstant P * P.k ≤ C₀)
    (hgrowth :
      (stateSourceMajorants P state b bLast
        ((l : ℂ) / (P.q : ℂ)) m).growth ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4)) :
    2 *
        (rationalTargetConjugateBound P (coordinatesForState state)
            state.support state.coeff P.h P.LzeroPlusOne b bLast J l m ^
          (13 ^ (oldRank + 1) - 1)) *
        ‖(commonDeltaDenominator P.h P.LzeroPlusOne
          (P.q ^ (J + 1)) m : ℂ)‖ ≤
      Real.exp (3 * sourceExponent P
        (C₀ * Real.log P.OmegaOld) / 4) := by
  refine (rationalLiouvilleProduct_le_exp_absorption
    P hJ state b bLast l hl m hm hgrowth).trans ?_
  apply Real.exp_le_exp.mpr
  unfold rationalLiouvilleAbsorptionConstant rationalHeightScale
  unfold sourceExponent VDPLParameters.Omega
  have hh : (P.h : ℝ) ≤ Real.log P.Bsrc := P.h_cast_le_log_Bsrc
  have hA : 0 ≤ 5 + P.k ^ (P.mu / 2) * (P.k + 32) := by
    have := rationalLiouvilleAbsorptionConstant_pos P
    simpa only [rationalLiouvilleAbsorptionConstant] using this.le
  have hcore : 0 ≤ P.OmegaOld * Real.log P.newHeight *
      Real.log P.OmegaOld :=
    mul_nonneg (mul_nonneg P.OmegaOld_pos.le P.log_newHeight_pos.le)
      P.log_OmegaOld_pos.le
  have hfirst := mul_le_mul_of_nonneg_left hh
    (mul_nonneg (mul_nonneg hA P.k_pos.le) hcore)
  have hC' :
      (5 + P.k ^ (P.mu / 2) * (P.k + 32)) * P.k ≤ C₀ / 4 := by
    calc
      (5 + P.k ^ (P.mu / 2) * (P.k + 32)) * P.k =
          (4 * rationalLiouvilleAbsorptionConstant P * P.k) / 4 := by
        unfold rationalLiouvilleAbsorptionConstant
        ring
      _ ≤ C₀ / 4 := div_le_div_of_nonneg_right hC (by norm_num)
  have hsecond := mul_le_mul_of_nonneg_right hC'
    (mul_nonneg hcore (log_Bsrc_pos P).le)
  have hC0 : 0 ≤ C₀ := by
    have hleft : 0 ≤
        4 * rationalLiouvilleAbsorptionConstant P * P.k :=
      mul_nonneg (mul_nonneg (by norm_num)
        (rationalLiouvilleAbsorptionConstant_pos P).le) P.k_pos.le
    exact hleft.trans hC
  calc
    (5 + P.k ^ (P.mu / 2) * (P.k + 32)) *
        ((P.h : ℝ) * P.k * (P.OmegaOld * Real.log P.newHeight) *
          Real.log P.OmegaOld) =
      (5 + P.k ^ (P.mu / 2) * (P.k + 32)) * P.k *
        (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld) * P.h := by ring
    _ ≤ (5 + P.k ^ (P.mu / 2) * (P.k + 32)) * P.k *
        (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld) *
          Real.log P.Bsrc := hfirst
    _ = ((5 + P.k ^ (P.mu / 2) * (P.k + 32)) * P.k) *
        (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld *
          Real.log P.Bsrc) := by ring
    _ ≤ (C₀ / 4) *
        (P.OmegaOld * Real.log P.newHeight * Real.log P.OmegaOld *
          Real.log P.Bsrc) := hsecond
    _ ≤ 3 * (C₀ * Real.log P.OmegaOld * P.OmegaOld *
        Real.log P.newHeight * Real.log P.Bsrc) / 4 := by
      have hprod : 0 ≤ C₀ * P.OmegaOld * Real.log P.newHeight *
          Real.log P.OmegaOld * Real.log P.Bsrc :=
        mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg hC0 P.OmegaOld_pos.le) P.log_newHeight_pos.le)
            P.log_OmegaOld_pos.le)
          (log_Bsrc_pos P).le
      nlinarith

/-- Direct lower bound for the exact rational Liouville threshold on the
full Lemma-5 grid. -/
theorem exp_neg_three_quarters_le_stateRationalLiouvilleThreshold
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (hJ : P.LevelOK J)
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (l : ℕ) (hl : l ≤ P.R (J + 1))
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep J)
    (C₀ : ℝ)
    (hC : 4 * rationalLiouvilleAbsorptionConstant P * P.k ≤ C₀)
    (hgrowth :
      (stateSourceMajorants P state b bLast
        ((l : ℂ) / (P.q : ℂ)) m).growth ≤
        Real.exp
          (sourceExponent P (P.C * Real.log P.OmegaOld) / 4)) :
    Real.exp (-3 * sourceExponent P
        (C₀ * Real.log P.OmegaOld) / 4) ≤
      stateRationalLiouvilleThreshold P J state b bLast l m := by
  apply BakerSourceOversizedConstantUniform.exp_neg_three_quarters_le_stateRationalLiouvilleThreshold
  exact rationalLiouvilleProduct_le_exp_three_quarters
    P hJ state b bLast l hl m hm C₀ hC hgrowth

end Erdos240.BakerSourceRationalLiouvilleLowerBounds

#print axioms Erdos240.BakerSourceRationalLiouvilleLowerBounds.rationalTargetConjugateBound_le
#print axioms Erdos240.BakerSourceRationalLiouvilleLowerBounds.rationalLiouvilleProduct_le_exp_three_quarters
#print axioms Erdos240.BakerSourceRationalLiouvilleLowerBounds.exp_neg_three_quarters_le_stateRationalLiouvilleThreshold
