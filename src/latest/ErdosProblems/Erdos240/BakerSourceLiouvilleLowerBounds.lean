/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.BakerSourceLiouvilleThresholds
import ErdosProblems.Erdos240.BakerSourceBudgetInequalities
import ErdosProblems.Erdos240.BakerLemma2Concrete

/-! # Explicit integral-target Liouville lower bounds -/

open scoped BigOperators NumberField
noncomputable section

namespace Erdos240.BakerSourceLiouvilleLowerBounds

open Erdos240 BakerLemma3Concrete BakerLemma3Instantiation
  BakerSourceLiouvilleThresholds BakerSourceState

theorem norm_commonDeltaDenominator_eq {oldRank : ℕ}
    (h deltaPowerBound den : ℕ) (m : VDPLMultiIndex (oldRank + 1)) :
    ‖(commonDeltaDenominator h deltaPowerBound den m : ℂ)‖ =
      (den : ℝ) ^ (2 * h * deltaPowerBound) *
        (Nat.lcmUpto h : ℝ) ^ (m 0) := by
  rw [commonDeltaDenominator]
  push_cast
  rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast,
    Complex.norm_natCast]

theorem norm_commonDeltaDenominator_le {oldRank : ℕ}
    (h deltaPowerBound den : ℕ) (m : VDPLMultiIndex (oldRank + 1)) :
    ‖(commonDeltaDenominator h deltaPowerBound den m : ℂ)‖ ≤
      (den : ℝ) ^ (2 * h * deltaPowerBound) *
        (4 : ℝ) ^ (h * m 0) := by
  rw [norm_commonDeltaDenominator_eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (Nat.lcmUpto h : ℝ) ^ (m 0) ≤ ((4 ^ h : ℕ) : ℝ) ^ (m 0) := by
      gcongr
      exact_mod_cast Erdos240.LcmBound.lcmUpto_le_four_pow h
    _ = (4 : ℝ) ^ (h * m 0) := by
      push_cast
      rw [← pow_mul]

theorem norm_commonDeltaDenominator_le_exp {oldRank : ℕ}
    (h deltaPowerBound den : ℕ) (m : VDPLMultiIndex (oldRank + 1))
    (hden : 0 < den) :
    ‖(commonDeltaDenominator h deltaPowerBound den m : ℂ)‖ ≤
      Real.exp
        (((2 * h * deltaPowerBound : ℕ) : ℝ) * Real.log den +
          ((h * m 0 : ℕ) : ℝ) * Real.log 4) := by
  refine (norm_commonDeltaDenominator_le h deltaPowerBound den m).trans ?_
  rw [Real.exp_add]
  apply mul_le_mul
  · exact VDPLParameters.pow_le_exp_of_mul_log_le
      (by exact_mod_cast hden) le_rfl
  · exact VDPLParameters.pow_le_exp_of_mul_log_le (by norm_num) le_rfl
  · positivity
  · positivity

def integralDenominatorAbsorptionConstant {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℝ :=
  8 * P.k * P.OmegaOld

theorem integralDenominatorAbsorptionConstant_pos {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    0 < integralDenominatorAbsorptionConstant P := by
  unfold integralDenominatorAbsorptionConstant
  exact mul_pos (mul_pos (by norm_num) P.k_pos) P.OmegaOld_pos

theorem log_k_le_k_rpow_sigma {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    Real.log P.k ≤ P.k ^ P.sigma := by
  have hseed : P.kSeedBase ≤ P.k ^ P.epsilon := by
    have h := Real.rpow_le_rpow P.kSeed_pos.le P.kSeed_lt_k.le
      P.epsilon_pos.le
    rwa [P.kSeed_rpow_epsilon_eq_kSeedBase] at h
  have hinv : P.epsilon⁻¹ ≤ P.k ^ P.epsilon := by
    calc
      P.epsilon⁻¹ = (P.kExponent : ℝ) := P.epsilon_inv_eq_kExponent
      _ ≤ P.kSeedBase := by
        rw [P.kExponent_eq]
        unfold VDPLParameters.kSeedBase
        push_cast
        have hr : (0 : ℝ) ≤ P.rank := by positivity
        nlinarith
      _ ≤ P.k ^ P.epsilon := hseed
  have hlog := Real.log_le_rpow_div P.k_pos.le P.epsilon_pos
  have hsq : P.k ^ P.epsilon / P.epsilon ≤
      P.k ^ P.epsilon * P.k ^ P.epsilon := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv
      (Real.rpow_pos_of_pos P.k_pos _).le
  have hsigma : 2 * P.epsilon ≤ P.sigma := by
    rw [P.epsilon_eq, P.sigma_eq]
    have hr : (0 : ℝ) < P.rank + 1 := by positivity
    field_simp
    nlinarith
  calc
    Real.log P.k ≤ P.k ^ P.epsilon / P.epsilon := hlog
    _ ≤ P.k ^ P.epsilon * P.k ^ P.epsilon := hsq
    _ = P.k ^ (2 * P.epsilon) := by
      rw [← Real.rpow_add P.k_pos]
      congr 1
      ring
    _ ≤ P.k ^ P.sigma :=
      Real.rpow_le_rpow_of_exponent_le P.one_le_k hsigma

theorem log_levelBound_le_four_mul_rpow_sigma_mul_logOmegaOld
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) :
    Real.log P.levelBound ≤
      4 * P.k ^ P.sigma * Real.log P.OmegaOld := by
  have hepsSigma : P.epsilon ≤ P.sigma := by
    rw [P.epsilon_eq, P.sigma_eq]
    have hr : (0 : ℝ) < P.rank + 1 := by positivity
    field_simp
    nlinarith
  have hkpow : P.k ^ (1 - (P.sigma - P.epsilon)) ≤ P.k := by
    calc
      P.k ^ (1 - (P.sigma - P.epsilon)) ≤ P.k ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le P.one_le_k (by linarith)
      _ = P.k := Real.rpow_one _
  have hrank : (1 : ℝ) ≤ 8 * P.rank := by
    have h : (1 : ℝ) ≤ P.rank := by exact_mod_cast P.one_le_rank
    nlinarith
  have hinv : (8 * (P.rank : ℝ))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hrank
  have hlevel : P.levelBound ≤
      P.k * P.OmegaOld * Real.log P.OmegaOld := by
    unfold VDPLParameters.levelBound
    have hpow0 : 0 ≤ P.k ^ (1 - (P.sigma - P.epsilon)) :=
      (Real.rpow_pos_of_pos P.k_pos _).le
    have hmul : (8 * (P.rank : ℝ))⁻¹ *
        P.k ^ (1 - (P.sigma - P.epsilon)) ≤ P.k := by
      simpa using mul_le_mul hinv hkpow hpow0 (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        hmul
        P.OmegaOld_pos.le)
      P.log_OmegaOld_pos.le
  have hloglevel : Real.log P.levelBound ≤
      Real.log (P.k * P.OmegaOld * Real.log P.OmegaOld) :=
    Real.log_le_log P.levelBound_pos hlevel
  have hformula : Real.log (P.k * P.OmegaOld * Real.log P.OmegaOld) =
      Real.log P.k + Real.log P.OmegaOld +
        Real.log (Real.log P.OmegaOld) := by
    rw [Real.log_mul (mul_ne_zero P.k_pos.ne' P.OmegaOld_pos.ne')
      P.log_OmegaOld_pos.ne',
      Real.log_mul P.k_pos.ne' P.OmegaOld_pos.ne']
  have hloglog : Real.log (Real.log P.OmegaOld) ≤
      Real.log P.OmegaOld := by
    have h := Real.log_le_sub_one_of_pos P.log_OmegaOld_pos
    linarith
  have hK : (1 : ℝ) ≤ P.k ^ P.sigma :=
    Real.one_le_rpow P.one_le_k P.sigma_pos.le
  have hL : (1 / 2 : ℝ) < Real.log P.OmegaOld := by
    nlinarith [Real.log_two_gt_d9, P.log_two_le_log_OmegaOld]
  calc
    Real.log P.levelBound ≤
        Real.log (P.k * P.OmegaOld * Real.log P.OmegaOld) := hloglevel
    _ = Real.log P.k + Real.log P.OmegaOld +
        Real.log (Real.log P.OmegaOld) := hformula
    _ ≤ P.k ^ P.sigma + 2 * Real.log P.OmegaOld := by
      linarith [log_k_le_k_rpow_sigma P]
    _ ≤ 4 * P.k ^ P.sigma * Real.log P.OmegaOld := by nlinarith

theorem level_mul_log_q_lt_four_mul_rpow_sigma_mul_logOmegaOld
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (hJ : P.LevelOK J) :
    (J : ℝ) * Real.log P.q <
      4 * P.k ^ P.sigma * Real.log P.OmegaOld := by
  have hpowpos : (0 : ℝ) < (P.q ^ J : ℕ) := by
    exact_mod_cast pow_pos (Nat.zero_lt_of_lt P.one_lt_q) J
  have hlog := Real.log_lt_log hpowpos hJ
  rw [show Real.log ((P.q ^ J : ℕ) : ℝ) =
      (J : ℝ) * Real.log P.q by
    push_cast
    rw [Real.log_pow]] at hlog
  exact hlog.trans_le
    (log_levelBound_le_four_mul_rpow_sigma_mul_logOmegaOld P)

theorem norm_state_commonDeltaDenominator_lt_exp_three_heightScale
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (hJ : P.LevelOK J)
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Slevel J) :
    ‖(commonDeltaDenominator P.h P.LzeroPlusOne (P.q ^ J) m : ℂ)‖ <
      Real.exp
        (3 * ((P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld)) := by
  have hqpow : 0 < P.q ^ J := pow_pos (Nat.zero_lt_of_lt P.one_lt_q) J
  refine (norm_commonDeltaDenominator_le_exp P.h P.LzeroPlusOne
    (P.q ^ J) m hqpow).trans_lt ?_
  apply Real.exp_lt_exp.mpr
  let B : ℝ := P.k * P.Omega * Real.log P.OmegaOld
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg P.k_pos.le P.Omega_pos.le)
      P.log_OmegaOld_pos.le
  have hm0 : m 0 ≤ P.Slevel J :=
    (VDPLMultiIndex.component_le_weight m 0).trans hm
  have hm0r : (m 0 : ℝ) ≤ P.Slevel J := by exact_mod_cast hm0
  have hS : (P.Slevel J : ℝ) ≤ B := by
    calc
      (P.Slevel J : ℝ) ≤ P.levelScale J := P.Slevel_cast_le J
      _ ≤ B := by
        unfold VDPLParameters.levelScale VDPLParameters.qInvPow
        have hinv : (((P.q ^ J : ℕ) : ℝ))⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (by exact_mod_cast
            (one_le_pow₀ (show 1 ≤ P.q from P.one_lt_q.le) :
              1 ≤ P.q ^ J))
        simpa only [B, mul_assoc, one_mul] using
          mul_le_mul_of_nonneg_right hinv hB0
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
          ((J : ℝ) * Real.log P.q) < (P.h : ℝ) * B := by
    have hJ0 : 0 ≤ (J : ℝ) * Real.log P.q :=
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
          ((J : ℝ) * Real.log P.q) ≤
        (2 * (P.h : ℝ) *
          ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega)) *
            ((J : ℝ) * Real.log P.q) :=
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
      2 * ((P.h : ℝ) * B) := by
    have hmB : (P.h : ℝ) * (m 0 : ℝ) ≤ (P.h : ℝ) * B :=
      mul_le_mul_of_nonneg_left (hm0r.trans hS) (by positivity)
    calc
      ((P.h : ℝ) * (m 0 : ℝ)) * Real.log 4 ≤
          ((P.h : ℝ) * B) * Real.log 4 :=
        mul_le_mul_of_nonneg_right hmB (Real.log_nonneg (by norm_num))
      _ ≤ ((P.h : ℝ) * B) * 2 :=
        mul_le_mul_of_nonneg_left hlog4 (mul_nonneg (by positivity) hB0)
      _ = 2 * ((P.h : ℝ) * B) := by ring
  rw [show Real.log ((P.q ^ J : ℕ) : ℝ) =
      (J : ℝ) * Real.log P.q by
    push_cast
    rw [Real.log_pow]]
  push_cast
  dsimp only [B] at hhead hlcm ⊢
  linarith

theorem exp_neg_four_heightScale_lt_stateIntegralLiouvilleThreshold
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (hJ : P.LevelOK J)
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Slevel J) :
    Real.exp (-(4 * ((P.h : ℝ) * P.k * P.Omega *
      Real.log P.OmegaOld))) < stateIntegralLiouvilleThreshold P J m := by
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  let D : ℝ := ‖(commonDeltaDenominator P.h P.LzeroPlusOne
    (P.q ^ J) m : ℂ)‖
  have hD : D < Real.exp (3 * H) := by
    simpa only [D, H] using
      norm_state_commonDeltaDenominator_lt_exp_three_heightScale P hJ m hm
  have hDpos : 0 < D :=
    lt_of_lt_of_le zero_lt_one (by
      simpa only [D] using one_le_norm_commonDeltaDenominator
        P.h P.LzeroPlusOne (P.q ^ J)
        (pow_ne_zero J (Nat.ne_of_gt
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
  have hden : D * 2 < Real.exp (4 * H) := by
    calc
      D * 2 < Real.exp (3 * H) * 2 :=
        mul_lt_mul_of_pos_right hD (by norm_num)
      _ < Real.exp (3 * H) * Real.exp H :=
        mul_lt_mul_of_pos_left htwo (Real.exp_pos _)
      _ = Real.exp (4 * H) := by
        rw [← Real.exp_add]
        congr 1
        ring
  change Real.exp (-(4 * H)) < _
  simp only [stateIntegralLiouvilleThreshold, one_pow, inv_one, D]
  rw [show Real.exp (-(4 * H)) = 1 / Real.exp (4 * H) by
    rw [one_div, ← Real.exp_neg]]
  rw [div_div]
  exact one_div_lt_one_div_of_lt (mul_pos hDpos (by norm_num)) hden

end Erdos240.BakerSourceLiouvilleLowerBounds

#print axioms Erdos240.BakerSourceLiouvilleLowerBounds.norm_state_commonDeltaDenominator_lt_exp_three_heightScale
#print axioms Erdos240.BakerSourceLiouvilleLowerBounds.exp_neg_four_heightScale_lt_stateIntegralLiouvilleThreshold
