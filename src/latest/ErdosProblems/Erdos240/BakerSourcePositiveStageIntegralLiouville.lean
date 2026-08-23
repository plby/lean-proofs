/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.BakerSourceLiouvilleLowerBounds

/-!
# Positive-stage integral Liouville lower bounds

At a positive inner stage of source Lemma 4, the derivative budget is at
most half the level scale.  This saves one full height unit in the common
Delta denominator.  The remaining factor `2` is absorbed by one positive
stage height unit.
-/

noncomputable section

namespace Erdos240.BakerSourcePositiveStageIntegralLiouville

open BakerLemma2Concrete
open BakerLemma3Instantiation
open BakerSourceLiouvilleLowerBounds
open BakerSourceLiouvilleThresholds

/-- Fixed height unit, named locally so this arithmetic module does not
depend on the analytic contour-growth layer. -/
def integralSourceHeightUnit {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) : ℝ :=
  (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld

/-- Positive-stage unit used to absorb the leading factor two. -/
def integralPositiveStageHeightUnit {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (t : ℕ) : ℝ :=
  (P.h : ℝ) * P.k ^
      (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ)) *
    P.Omega * Real.log P.OmegaOld

theorem one_le_integralPositiveStageHeightUnit {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) (t : ℕ) :
    1 ≤ integralPositiveStageHeightUnit P t := by
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
  unfold integralPositiveStageHeightUnit
  calc
    (1 : ℝ) = 2 * 1 * 1 * (1 / 2) := by ring
    _ ≤ (P.h : ℝ) *
        P.k ^ (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ)) *
        P.Omega * Real.log P.OmegaOld :=
      mul_le_mul hhkO hlog (by norm_num)
        (mul_nonneg
          (mul_nonneg (by positivity) (Real.rpow_pos_of_pos P.k_pos _).le)
          P.Omega_pos.le)

theorem positiveStageBudget_cast_le_half_levelScale {oldRank : ℕ}
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
    _ ≤ (P.Slevel N : ℝ) / 2 := Nat.floor_le (by positivity)
    _ ≤ P.levelScale N / 2 := by
      gcongr
      exact P.Slevel_cast_le N

/-- At every positive Lemma-4 inner stage, the common Delta denominator
costs strictly less than two fixed source height units. -/
theorem norm_commonDeltaDenominator_lt_exp_two_sourceHeightUnit
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {N : ℕ} (hN : P.LevelOK N)
    (t : ℕ) (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1)) :
    ‖(commonDeltaDenominator P.h P.LzeroPlusOne (P.q ^ N) m : ℂ)‖ <
      Real.exp (2 * integralSourceHeightUnit P) := by
  have hqpow : 0 < P.q ^ N :=
    pow_pos (Nat.zero_lt_of_lt P.one_lt_q) N
  refine (norm_commonDeltaDenominator_le_exp P.h P.LzeroPlusOne
    (P.q ^ N) m hqpow).trans_lt ?_
  apply Real.exp_lt_exp.mpr
  let B : ℝ := P.k * P.Omega * Real.log P.OmegaOld
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (mul_nonneg P.k_pos.le P.Omega_pos.le)
      P.log_OmegaOld_pos.le
  have hm0 : m 0 ≤ P.lemmaFourBudget N (t + 1) :=
    (VDPLMultiIndex.component_le_weight m 0).trans hm
  have hm0r : (m 0 : ℝ) ≤ P.lemmaFourBudget N (t + 1) := by
    exact_mod_cast hm0
  have hbudget := positiveStageBudget_cast_le_half_levelScale P N t
  have hbudgetB : (P.lemmaFourBudget N (t + 1) : ℝ) ≤ B / 2 := by
    refine hbudget.trans ?_
    apply div_le_div_of_nonneg_right _ (by norm_num)
    unfold VDPLParameters.levelScale VDPLParameters.qInvPow
    have hinv : (((P.q ^ N : ℕ) : ℝ))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by exact_mod_cast
        (one_le_pow₀ (show 1 ≤ P.q from P.one_lt_q.le) :
          1 ≤ P.q ^ N))
    simpa only [B, mul_assoc, one_mul] using
      mul_le_mul_of_nonneg_right hinv hB0
  have hL : (P.LzeroPlusOne : ℝ) ≤
      (1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega := by
    simpa only [VDPLParameters.LzeroScale] using P.LzeroPlusOne_cast_le
  have hNlog :=
    level_mul_log_q_lt_four_mul_rpow_sigma_mul_logOmegaOld P hN
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    rw [Real.log_four_eq]
    nlinarith [Real.log_two_lt_d9]
  have hhead :
      (2 * (P.h : ℝ) * P.LzeroPlusOne) *
          ((N : ℝ) * Real.log P.q) < (P.h : ℝ) * B := by
    have hN0 : 0 ≤ (N : ℝ) * Real.log P.q :=
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
          ((N : ℝ) * Real.log P.q) ≤
        (2 * (P.h : ℝ) *
          ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega)) *
            ((N : ℝ) * Real.log P.q) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL (by positivity)) hN0
      _ < (2 * (P.h : ℝ) *
          ((1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega)) *
            (4 * P.k ^ P.sigma * Real.log P.OmegaOld) :=
        mul_lt_mul_of_pos_left hNlog hcoef
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
            rw [k_rpow_one_sub_sigma_mul_rpow_sigma P]
            ring
          _ = (P.h : ℝ) *
                (P.k * P.Omega * Real.log P.OmegaOld) := by ring
  have hlcm : ((P.h : ℝ) * m 0) * Real.log 4 ≤
      (P.h : ℝ) * B := by
    have hmB : (m 0 : ℝ) ≤ B / 2 := hm0r.trans hbudgetB
    have hhm : (P.h : ℝ) * (m 0 : ℝ) ≤
        (P.h : ℝ) * (B / 2) :=
      mul_le_mul_of_nonneg_left hmB (by positivity)
    calc
      ((P.h : ℝ) * (m 0 : ℝ)) * Real.log 4 ≤
          ((P.h : ℝ) * (B / 2)) * Real.log 4 :=
        mul_le_mul_of_nonneg_right hhm (Real.log_nonneg (by norm_num))
      _ ≤ ((P.h : ℝ) * (B / 2)) * 2 :=
        mul_le_mul_of_nonneg_left hlog4
          (mul_nonneg (by positivity) (div_nonneg hB0 (by norm_num)))
      _ = (P.h : ℝ) * B := by ring
  rw [show Real.log ((P.q ^ N : ℕ) : ℝ) =
      (N : ℝ) * Real.log P.q by
    push_cast
    rw [Real.log_pow]]
  push_cast
  unfold integralSourceHeightUnit
  dsimp only [B] at hhead hlcm ⊢
  linarith

/-- Positive-stage integral Liouville lower bound.  The exact stage unit
absorbs the unavoidable leading factor `2` in the threshold. -/
theorem exp_neg_two_sourceHeightUnit_add_positiveStageHeightUnit_lt_threshold
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {N : ℕ} (hN : P.LevelOK N)
    (t : ℕ) (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1)) :
    Real.exp (-(2 * integralSourceHeightUnit P +
        integralPositiveStageHeightUnit P t)) <
      stateIntegralLiouvilleThreshold P N m := by
  let H : ℝ := integralSourceHeightUnit P
  let T : ℝ := integralPositiveStageHeightUnit P t
  let D : ℝ := ‖(commonDeltaDenominator P.h P.LzeroPlusOne
    (P.q ^ N) m : ℂ)‖
  have hD : D < Real.exp (2 * H) := by
    simpa only [D, H] using
      norm_commonDeltaDenominator_lt_exp_two_sourceHeightUnit P hN t m hm
  have hDpos : 0 < D :=
    lt_of_lt_of_le zero_lt_one (by
      simpa only [D] using one_le_norm_commonDeltaDenominator
        P.h P.LzeroPlusOne (P.q ^ N)
        (pow_ne_zero N (Nat.ne_of_gt
          (Nat.zero_lt_of_lt P.one_lt_q))) m)
  have hT : 1 ≤ T := by
    simpa only [T] using one_le_integralPositiveStageHeightUnit P t
  have htwo : (2 : ℝ) < Real.exp T :=
    Real.exp_one_gt_two.trans_le (Real.exp_le_exp.mpr hT)
  have hden : D * 2 < Real.exp (2 * H + T) := by
    calc
      D * 2 < Real.exp (2 * H) * 2 :=
        mul_lt_mul_of_pos_right hD (by norm_num)
      _ < Real.exp (2 * H) * Real.exp T :=
        mul_lt_mul_of_pos_left htwo (Real.exp_pos _)
      _ = Real.exp (2 * H + T) := by rw [Real.exp_add]
  change Real.exp (-(2 * H + T)) < _
  simp only [stateIntegralLiouvilleThreshold, one_pow, inv_one, D]
  rw [show Real.exp (-(2 * H + T)) = 1 / Real.exp (2 * H + T) by
    rw [one_div, ← Real.exp_neg]]
  rw [div_div]
  exact one_div_lt_one_div_of_lt (mul_pos hDpos (by norm_num)) hden

/-- Formula-level version of the stage-sensitive lower bound, convenient
for consumers using their own names for the two height units. -/
theorem exp_neg_positiveStage_formula_lt_stateIntegralLiouvilleThreshold
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {N : ℕ} (hN : P.LevelOK N)
    (t : ℕ) (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1)) :
    Real.exp (-(2 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld) +
        (P.h : ℝ) * P.k ^
          (1 - P.sigma + P.epsilon * ((t + 1 : ℕ) : ℝ)) *
          P.Omega * Real.log P.OmegaOld)) <
      stateIntegralLiouvilleThreshold P N m := by
  simpa only [integralSourceHeightUnit, integralPositiveStageHeightUnit] using
    exp_neg_two_sourceHeightUnit_add_positiveStageHeightUnit_lt_threshold
      P hN t m hm

/-- Direct comparison at the outer-remainder exponent used by positive
source Lemma-4 stages. -/
theorem exp_neg_eight_positiveStage_lt_stateIntegralLiouvilleThreshold
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {N : ℕ} (hN : P.LevelOK N)
    (t : ℕ) (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.lemmaFourBudget N (t + 1)) :
    Real.exp (-(2 * integralSourceHeightUnit P +
        8 * integralPositiveStageHeightUnit P t)) <
      stateIntegralLiouvilleThreshold P N m := by
  have hT : 0 < integralPositiveStageHeightUnit P t :=
    lt_of_lt_of_le zero_lt_one (one_le_integralPositiveStageHeightUnit P t)
  have hexp :
      Real.exp (-(2 * integralSourceHeightUnit P +
          8 * integralPositiveStageHeightUnit P t)) <
        Real.exp (-(2 * integralSourceHeightUnit P +
          integralPositiveStageHeightUnit P t)) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  exact hexp.trans
    (exp_neg_two_sourceHeightUnit_add_positiveStageHeightUnit_lt_threshold
      P hN t m hm)

end Erdos240.BakerSourcePositiveStageIntegralLiouville

#print axioms
  Erdos240.BakerSourcePositiveStageIntegralLiouville.norm_commonDeltaDenominator_lt_exp_two_sourceHeightUnit
#print axioms
  Erdos240.BakerSourcePositiveStageIntegralLiouville.exp_neg_two_sourceHeightUnit_add_positiveStageHeightUnit_lt_threshold
#print axioms
  Erdos240.BakerSourcePositiveStageIntegralLiouville.exp_neg_positiveStage_formula_lt_stateIntegralLiouvilleThreshold
#print axioms
  Erdos240.BakerSourcePositiveStageIntegralLiouville.exp_neg_eight_positiveStage_lt_stateIntegralLiouvilleThreshold
