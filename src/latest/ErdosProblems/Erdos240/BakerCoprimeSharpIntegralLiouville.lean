/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceLiouvilleLowerBounds

/-!
# Sharp integral Liouville loss at a successor level

For the coprime completion the relevant state has level `J + 1`.  Retaining
the factor `qInvPow (J + 1) <= 1 / 13` in the lcm part of the common
denominator sharpens the generic three-height-unit estimate to one and a
half height units.  The extra factor two in the integral Liouville
threshold then costs at most one further height unit.
-/

open scoped BigOperators NumberField
noncomputable section

namespace Erdos240.BakerCoprimeSharpIntegralLiouville

open Erdos240 BakerLemma3Concrete BakerLemma3Instantiation
  BakerSourceLiouvilleLowerBounds BakerSourceLiouvilleThresholds
  BakerSourceState

theorem qInvPow_succ_le_one_thirteenth {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (J : ℕ) :
    P.qInvPow (J + 1) ≤ (1 / 13 : ℝ) := by
  have hJ : P.qInvPow J ≤ 1 := by
    have hmono := P.qInvPow_antitone (Nat.zero_le J)
    simpa [VDPLParameters.qInvPow] using hmono
  rw [P.qInvPow_succ, P.q_eq]
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 13)).2 hJ

/-- At a successor level the common denominator costs less than `3H/2`,
where `H = h * k * Omega * log OmegaOld`. -/
theorem norm_state_successor_commonDeltaDenominator_lt_exp_three_halves_heightScale
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (hJ : P.LevelOK (J + 1))
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Slevel (J + 1)) :
    ‖(commonDeltaDenominator P.h P.LzeroPlusOne
        (P.q ^ (J + 1)) m : ℂ)‖ <
      Real.exp
        ((3 / 2 : ℝ) *
          ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) := by
  have hqpow : 0 < P.q ^ (J + 1) :=
    pow_pos (Nat.zero_lt_of_lt P.one_lt_q) _
  refine (norm_commonDeltaDenominator_le_exp P.h P.LzeroPlusOne
    (P.q ^ (J + 1)) m hqpow).trans_lt ?_
  apply Real.exp_lt_exp.mpr
  let B : ℝ := P.k * P.Omega * Real.log P.OmegaOld
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg P.k_pos.le P.Omega_pos.le)
      P.log_OmegaOld_pos.le
  have hm0 : m 0 ≤ P.Slevel (J + 1) :=
    (VDPLMultiIndex.component_le_weight m 0).trans hm
  have hm0r : (m 0 : ℝ) ≤ P.Slevel (J + 1) := by
    exact_mod_cast hm0
  have hS : (P.Slevel (J + 1) : ℝ) ≤ (1 / 13 : ℝ) * B := by
    calc
      (P.Slevel (J + 1) : ℝ) ≤ P.levelScale (J + 1) :=
        P.Slevel_cast_le (J + 1)
      _ = P.qInvPow (J + 1) * B := by
        unfold VDPLParameters.levelScale
        dsimp only [B]
        ring
      _ ≤ (1 / 13 : ℝ) * B :=
        mul_le_mul_of_nonneg_right
          (qInvPow_succ_le_one_thirteenth P J) hB0
  have hL : (P.LzeroPlusOne : ℝ) ≤
      (1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega := by
    simpa only [VDPLParameters.LzeroScale] using P.LzeroPlusOne_cast_le
  have hJlog :=
    level_mul_log_q_lt_four_mul_rpow_sigma_mul_logOmegaOld P hJ
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    rw [Real.log_four_eq]
    nlinarith [Real.log_two_lt_d9]
  have hhead :
      (2 * (P.h : ℝ) * P.LzeroPlusOne) *
          (((J + 1 : ℕ) : ℝ) * Real.log P.q) <
        (P.h : ℝ) * B := by
    have hJ0 : 0 ≤ ((J + 1 : ℕ) : ℝ) * Real.log P.q :=
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
          (mul_le_mul_of_nonneg_left hL (by positivity)) hJ0
      _ < (2 * (P.h : ℝ) *
          ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega)) *
            (4 * P.k ^ P.sigma * Real.log P.OmegaOld) :=
        mul_lt_mul_of_pos_left hJlog hcoef
      _ = (P.h : ℝ) * B := by
        dsimp only [B]
        calc
          (2 * (P.h : ℝ) *
              ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega)) *
                (4 * P.k ^ P.sigma * Real.log P.OmegaOld) =
              (P.h : ℝ) * P.Omega * Real.log P.OmegaOld *
                (P.k ^ (1 - P.sigma) * P.k ^ P.sigma) := by ring
          _ = (P.h : ℝ) * P.k * P.Omega *
                Real.log P.OmegaOld := by
            rw [BakerLemma2Concrete.k_rpow_one_sub_sigma_mul_rpow_sigma P]
            ring
          _ = (P.h : ℝ) * B := by
            dsimp only [B]
            ring
  have hlcm : ((P.h : ℝ) * m 0) * Real.log 4 ≤
      (2 / 13 : ℝ) * ((P.h : ℝ) * B) := by
    have hmB : (P.h : ℝ) * (m 0 : ℝ) ≤
        (P.h : ℝ) * ((1 / 13 : ℝ) * B) :=
      mul_le_mul_of_nonneg_left (hm0r.trans hS) (by positivity)
    calc
      ((P.h : ℝ) * (m 0 : ℝ)) * Real.log 4 ≤
          ((P.h : ℝ) * ((1 / 13 : ℝ) * B)) * Real.log 4 :=
        mul_le_mul_of_nonneg_right hmB (Real.log_nonneg (by norm_num))
      _ ≤ ((P.h : ℝ) * ((1 / 13 : ℝ) * B)) * 2 :=
        mul_le_mul_of_nonneg_left hlog4
          (mul_nonneg (by positivity)
            (mul_nonneg (by norm_num) hB0))
      _ = (2 / 13 : ℝ) * ((P.h : ℝ) * B) := by ring
  rw [show Real.log ((P.q ^ (J + 1) : ℕ) : ℝ) =
      (((J + 1 : ℕ) : ℝ)) * Real.log P.q by
    push_cast
    rw [Real.log_pow]
    simp only [Nat.cast_add, Nat.cast_one]]
  push_cast at hhead hlcm ⊢
  have hHB0 : 0 ≤ (P.h : ℝ) * B :=
    mul_nonneg (by positivity) hB0
  dsimp only [B] at hhead hlcm hHB0 ⊢
  nlinarith

/-- The integral Liouville threshold at a successor level is strictly
larger than `exp (-5H/2)`. -/
theorem exp_neg_five_halves_heightScale_lt_successor_stateIntegralLiouvilleThreshold
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ}
    (hJ : P.LevelOK (J + 1))
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Slevel (J + 1)) :
    Real.exp
        (-((5 / 2 : ℝ) *
          ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld))) <
      stateIntegralLiouvilleThreshold P (J + 1) m := by
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  let D : ℝ := ‖(commonDeltaDenominator P.h P.LzeroPlusOne
    (P.q ^ (J + 1)) m : ℂ)‖
  have hD : D < Real.exp ((3 / 2 : ℝ) * H) := by
    simpa only [D, H] using
      norm_state_successor_commonDeltaDenominator_lt_exp_three_halves_heightScale
        P hJ m hm
  have hDpos : 0 < D :=
    lt_of_lt_of_le zero_lt_one (by
      simpa only [D] using one_le_norm_commonDeltaDenominator
        P.h P.LzeroPlusOne (P.q ^ (J + 1))
        (pow_ne_zero (J + 1) (Nat.ne_of_gt
          (Nat.zero_lt_of_lt P.one_lt_q))) m)
  have hH : 1 < H := by
    have hscale := BakerLemma2Concrete.six_lt_initial_levelScale P
    rw [BakerLemma2Concrete.initial_levelScale_formula] at hscale
    dsimp only [H]
    have hh : (1 : ℝ) ≤ P.h := by exact_mod_cast P.one_le_h
    nlinarith [mul_lt_mul_of_pos_left hscale (show (0 : ℝ) < P.h by
      exact_mod_cast P.h_pos)]
  have htwo : (2 : ℝ) < Real.exp H :=
    Real.exp_one_gt_two.trans (Real.exp_lt_exp.mpr hH)
  have hden : D * 2 < Real.exp ((5 / 2 : ℝ) * H) := by
    calc
      D * 2 < Real.exp ((3 / 2 : ℝ) * H) * 2 :=
        mul_lt_mul_of_pos_right hD (by norm_num)
      _ < Real.exp ((3 / 2 : ℝ) * H) * Real.exp H :=
        mul_lt_mul_of_pos_left htwo (Real.exp_pos _)
      _ = Real.exp ((5 / 2 : ℝ) * H) := by
        rw [← Real.exp_add]
        congr 1
        ring
  change Real.exp (-((5 / 2 : ℝ) * H)) < _
  simp only [stateIntegralLiouvilleThreshold, one_pow, inv_one, D]
  rw [show Real.exp (-((5 / 2 : ℝ) * H)) =
      1 / Real.exp ((5 / 2 : ℝ) * H) by
    rw [one_div, ← Real.exp_neg]]
  rw [div_div]
  exact one_div_lt_one_div_of_lt (mul_pos hDpos (by norm_num)) hden

end Erdos240.BakerCoprimeSharpIntegralLiouville

#print axioms Erdos240.BakerCoprimeSharpIntegralLiouville.norm_state_successor_commonDeltaDenominator_lt_exp_three_halves_heightScale
#print axioms Erdos240.BakerCoprimeSharpIntegralLiouville.exp_neg_five_halves_heightScale_lt_successor_stateIntegralLiouvilleThreshold
