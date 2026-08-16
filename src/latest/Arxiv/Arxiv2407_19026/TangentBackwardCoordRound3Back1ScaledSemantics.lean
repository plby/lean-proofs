import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound3Back1ScaledFinal
import Arxiv.Arxiv2407_19026.TangentBackwardCoordBounds

/-! Semantic bridge for the scaled round-3 backward-coordinate certificates. -/

namespace Arxiv2407_19026

namespace BackwardCoordRound3Back1Bounds

noncomputable def backwardBlueFitRound3Back1 (z : ℝ) : ℝ :=
  9751545159 / 1000000000000 +
    29298905659 / 25000000000 * z -
    91718791273 / 62500000000 * z ^ 2 +
    1098470325011 / 1000000000000 * z ^ 3 -
    352859905579 / 1000000000000 * z ^ 4 -
    634369 / 1000000000000

end BackwardCoordRound3Back1Bounds

namespace BackwardCoordRound3Back1Certificate

noncomputable section

open BackwardCoordRound3Back1Bounds

private lemma coord_scaled_ints_eval
    (coefficients : List ℤ) (z : ℝ) :
    (coordScaledInts coefficients).eval z =
      evalIntegerPower coefficients z := by
  simp [coordScaledInts, ScaledIntegerPower.eval_ofIntegers]

private lemma coord_scaled_rats_eval (scale : ℕ)
    (coefficients : List ℤ) (z : ℝ)
    (hscale : scale ≠ 0 := by norm_num) :
    (coordScaledRats scale coefficients hscale).eval z =
      evalIntegerPower coefficients z / scale := by
  rfl

private lemma coord_scaled_constant_eval
    (numerator : ℤ) (denominator : ℕ) (z : ℝ)
    (hdenominator : denominator ≠ 0 := by norm_num) :
    (coordScaledConstant numerator denominator hdenominator).eval z =
      numerator / denominator := by
  exact ScaledIntegerPower.eval_constant
    numerator denominator hdenominator z

lemma coord_scaled_z_eval (z : ℝ) :
    coordScaledZ.eval z = z := by
  norm_num [coordScaledZ, coord_scaled_ints_eval,
    evalIntegerPower]

lemma coord_scaled_t_eval (z : ℝ) :
    coordScaledT.eval z = r3Back1TReal z := by
  rw [coordScaledT, coordScaledComp,
    ScaledIntegerPower.eval_comp]
  norm_num [coordScaledRats,
    ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, r3Back1TReal,
    tangentLocalPoly, tangentRatHorner,
    TangentAffine.r3Back1Cs]
  ring

lemma coord_scaled_blue_fit_eval (z : ℝ) :
    coordScaledBlueFit.eval z =
      backwardBlueFitRound3Back1 z := by
  norm_num [coordScaledBlueFit, coordScaledRats,
    ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, backwardBlueFitRound3Back1]
  ring

lemma coord_scaled_taylor_nine_eval (z : ℝ) :
    coordScaledTaylorNine.eval z =
      KernelBounds.expNegTaylor9 z := by
  norm_num [coordScaledTaylorNine, coordScaledRats,
    ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, KernelBounds.expNegTaylor9,
    Finset.sum_range_succ, Nat.factorial]
  ring

lemma coord_scaled_error_ten_eval (z : ℝ) :
    coordScaledErrorTen.eval z =
      KernelBounds.expNegError10 z := by
  norm_num [coordScaledErrorTen, coordScaledRats,
    ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, KernelBounds.expNegError10,
    Nat.factorial]
  ring

lemma coord_scaled_new_correction_eval (z : ℝ) :
    coordScaledNewCorrection.eval z =
      mediumCorrectionPolynomial (3 / 100) z := by
  norm_num [coordScaledNewCorrection, coordScaledRats,
    ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, mediumCorrectionPolynomial]
  ring

lemma coord_scaled_q_eval (z : ℝ) :
    coordScaledQ.eval z = backwardQLower (3 / 100) z := by
  rw [coordScaledQ, coordScaledSub,
    ScaledIntegerPower.eval_sub, coordScaledNeg,
    ScaledIntegerPower.eval_neg, coordScaledMul,
    ScaledIntegerPower.eval_mul, coordScaledScaleBy,
    ScaledIntegerPower.eval_scaleBy,
    coord_scaled_new_correction_eval,
    coord_scaled_taylor_nine_eval,
    coord_scaled_error_ten_eval]
  norm_num [backwardQLower]

lemma coord_scaled_r_eval (z : ℝ) :
    coordScaledR.eval z =
      backwardQLower (3 / 100) z + 3 / 10 := by
  rw [coordScaledR, coordScaledAdd,
    ScaledIntegerPower.eval_add, coord_scaled_q_eval]
  norm_num [coordScaledConstant,
    ScaledIntegerPower.eval_constant]

lemma coord_scaled_exp_series_eval (z : ℝ) :
    coordScaledExpSeries.eval z =
      let r := backwardQLower (3 / 100) z + 3 / 10
      1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 := by
  simp only [coordScaledExpSeries, coordScaledAdd,
    coordScaledScaleBy, coordScaledPow,
    ScaledIntegerPower.eval_add,
    ScaledIntegerPower.eval_scaleBy,
    ScaledIntegerPower.eval_pow,
    coord_scaled_ints_eval, coord_scaled_r_eval]
  norm_num [evalIntegerPower]
  ring

lemma coord_scaled_exp_point_three_eval (z : ℝ) :
    coordScaledExpPointThreeLower.eval z =
      KernelBounds.expNegTaylor9 (3 / 10) -
        KernelBounds.expNegError10 (3 / 10) := by
  simp only [coordScaledExpPointThreeLower, coordScaledSub,
    ScaledIntegerPower.eval_sub, coordScaledComp,
    ScaledIntegerPower.eval_comp]
  rw [coord_scaled_taylor_nine_eval,
    coord_scaled_error_ten_eval]
  norm_num [coordScaledConstant,
    ScaledIntegerPower.eval_constant]

lemma coord_scaled_exp_q_lower_eval (z : ℝ) :
    coordScaledExpQLower.eval z =
      backwardExpQLower (3 / 100) z := by
  rw [coordScaledExpQLower, coordScaledMul,
    ScaledIntegerPower.eval_mul,
    coord_scaled_exp_point_three_eval,
    coord_scaled_exp_series_eval]
  rfl

lemma coord_scaled_blue_numerator_expression_eval (z : ℝ)
    (hz : 1 + z ≠ 0) :
    coordScaledBlueNumerator.eval z =
      (backwardBlueRawLower (3 / 100) z -
        backwardBlueFitRound3Back1 z) * (1 + z) := by
  simp only [coordScaledBlueNumerator, coordScaledSub,
    ScaledIntegerPower.eval_sub, coordScaledMul,
    ScaledIntegerPower.eval_mul]
  rw [coord_scaled_z_eval,
    coord_scaled_exp_q_lower_eval,
    coord_scaled_blue_fit_eval, coord_scaled_ints_eval]
  norm_num [evalIntegerPower, backwardBlueRawLower]
  field_simp [hz]

lemma coord_scaled_exp_lower_five_eval (z : ℝ) :
    coordScaledExpLowerFive.eval z = backwardExpLower5 z := by
  norm_num [coordScaledExpLowerFive, coordScaledRats,
    ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, backwardExpLower5,
    backwardExpTaylor5, backwardExpError6,
    Finset.sum_range_succ, Nat.factorial]
  ring

lemma coord_scaled_mu_eval (z : ℝ) :
    coordScaledMu.eval z = backwardMuLower z := by
  rw [coordScaledMu, coordScaledMul,
    ScaledIntegerPower.eval_mul, coord_scaled_z_eval,
    coord_scaled_exp_lower_five_eval]
  rfl

lemma coord_scaled_one_minus_mu_eval (z : ℝ) :
    coordScaledOneMinusMu.eval z = 1 - backwardMuLower z := by
  rw [coordScaledOneMinusMu, coordScaledSub,
    ScaledIntegerPower.eval_sub, coord_scaled_ints_eval,
    coord_scaled_mu_eval]
  norm_num [evalIntegerPower]

lemma coord_scaled_t_base_eval (z : ℝ) :
    coordScaledTBase.eval z =
      r3Back1TReal z * (1 + r3Back1TReal z) ^ 7 := by
  rw [coordScaledTBase, coordScaledMul,
    ScaledIntegerPower.eval_mul, coord_scaled_t_eval,
    coordScaledPow, ScaledIntegerPower.eval_pow,
    coordScaledAdd, ScaledIntegerPower.eval_add,
    coord_scaled_ints_eval, coord_scaled_t_eval]
  norm_num [evalIntegerPower]

lemma coord_scaled_den_eval (z : ℝ) :
    coordScaledDen.eval z =
      r3Back1TReal z * (1 + r3Back1TReal z) ^ 7 *
        (1 - backwardMuLower z) := by
  rw [coordScaledDen, coordScaledMul,
    ScaledIntegerPower.eval_mul, coord_scaled_t_base_eval,
    coord_scaled_one_minus_mu_eval]

lemma coord_scaled_log_four_numerator_eval (z : ℝ) :
    coordScaledLogFourNumerator.eval z =
      (r3Back1TReal z - 1) *
        (105 * r3Back1TReal z ^ 8 -
          136 * r3Back1TReal z ^ 7 +
          5212 * r3Back1TReal z ^ 6 +
          1096 * r3Back1TReal z ^ 5 +
          14326 * r3Back1TReal z ^ 4 +
          1096 * r3Back1TReal z ^ 3 +
          5212 * r3Back1TReal z ^ 2 -
          136 * r3Back1TReal z + 105) := by
  simp only [coordScaledLogFourNumerator,
    coordScaledSub, coordScaledMul, coordScaledAdd,
    coordScaledScaleBy, coordScaledPow,
    ScaledIntegerPower.eval_sub,
    ScaledIntegerPower.eval_mul,
    ScaledIntegerPower.eval_add,
    ScaledIntegerPower.eval_scaleBy,
    ScaledIntegerPower.eval_pow,
    coord_scaled_t_eval, coord_scaled_ints_eval]
  norm_num [evalIntegerPower]
  all_goals ring_nf
  all_goals simp

lemma coord_scaled_coord_log_upper_eval
    (p : CoordScaledPower) (z : ℝ) :
    (coordScaledCoordLogUpper p).eval z =
      tangentCoordLogUpper (p.eval z) := by
  simp only [coordScaledCoordLogUpper,
    coordScaledSub, coordScaledScaleBy, coordScaledComp,
    ScaledIntegerPower.eval_sub,
    ScaledIntegerPower.eval_scaleBy,
    ScaledIntegerPower.eval_comp]
  norm_num [coordScaledInts, coordScaledRats,
    coordScaledConstant, ScaledIntegerPower.eval_ofIntegers,
    ScaledIntegerPower.eval_constant,
    evalIntegerPower, tangentCoordLogUpper]
  ring

lemma coord_scaled_old_correction_eval (z : ℝ) :
    coordScaledOldCorrectionAtT.eval z =
      mediumCorrectionPolynomial (33 / 1000) (r3Back1TReal z) := by
  rw [coordScaledOldCorrectionAtT, coordScaledComp,
    ScaledIntegerPower.eval_comp, coord_scaled_t_eval]
  norm_num [coordScaledRats,
    ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, mediumCorrectionPolynomial]
  ring

lemma coord_scaled_taylor_five_at_t_eval (z : ℝ) :
    coordScaledTaylorFiveAtT.eval z =
      backwardExpTaylor5 (r3Back1TReal z) := by
  rw [coordScaledTaylorFiveAtT, coordScaledComp,
    ScaledIntegerPower.eval_comp, coord_scaled_t_eval]
  norm_num [coordScaledRats,
    ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, backwardExpTaylor5,
    Finset.sum_range_succ, Nat.factorial]
  ring

lemma coord_scaled_error_six_at_t_eval (z : ℝ) :
    coordScaledErrorSixAtT.eval z =
      backwardExpError6 (r3Back1TReal z) := by
  rw [coordScaledErrorSixAtT, coordScaledComp,
    ScaledIntegerPower.eval_comp, coord_scaled_t_eval]
  norm_num [coordScaledRats,
    ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, backwardExpError6, Nat.factorial]
  ring

lemma coord_scaled_b_other_eval (z : ℝ) :
    coordScaledBOther.eval z =
      tangentCoordLogUpper (1 + r3Back1TReal z) +
        mediumCorrectionPolynomial (33 / 1000) (r3Back1TReal z) *
          backwardExpTaylor5 (r3Back1TReal z) +
        (1 / 4) * backwardExpError6 (r3Back1TReal z) := by
  simp only [coordScaledBOther, coordScaledAdd,
    coordScaledMul, coordScaledScaleBy,
    ScaledIntegerPower.eval_add,
    ScaledIntegerPower.eval_mul,
    ScaledIntegerPower.eval_scaleBy,
    coord_scaled_coord_log_upper_eval,
    coord_scaled_old_correction_eval,
    coord_scaled_taylor_five_at_t_eval,
    coord_scaled_error_six_at_t_eval]
  rw [coord_scaled_ints_eval, coord_scaled_t_eval]
  norm_num [evalIntegerPower]
  ring

lemma coord_scaled_log_upper_five_loss_eval
    (p : CoordScaledPower) (z : ℝ) :
    (coordScaledLogUpperFiveLoss p).eval z =
      backwardLogUpperBelowFive (1 - p.eval z) := by
  rw [coordScaledLogUpperFiveLoss, coordScaledNeg,
    ScaledIntegerPower.eval_neg, coordScaledComp,
    ScaledIntegerPower.eval_comp]
  norm_num [coordScaledRats,
    ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, backwardLogUpperBelowFive]
  ring

lemma coord_scaled_b_log_numerator_eval (z : ℝ)
    (ht0 : r3Back1TReal z ≠ 0)
    (ht1 : r3Back1TReal z + 1 ≠ 0) :
    coordScaledBLogNumerator.eval z =
      (backwardLogLowerFourClosed (r3Back1TReal z) -
          tangentCoordLogUpper (1 + r3Back1TReal z) -
          mediumCorrectionPolynomial (33 / 1000) (r3Back1TReal z) *
            backwardExpTaylor5 (r3Back1TReal z) -
          (1 / 4) * backwardExpError6 (r3Back1TReal z)) *
        (r3Back1TReal z * (1 + r3Back1TReal z) ^ 7 *
          (1 - backwardMuLower z)) := by
  simp only [coordScaledBLogNumerator, coordScaledSub,
    ScaledIntegerPower.eval_sub, coordScaledScaleBy,
    ScaledIntegerPower.eval_scaleBy, coordScaledMul,
    ScaledIntegerPower.eval_mul]
  rw [coord_scaled_log_four_numerator_eval,
    coord_scaled_one_minus_mu_eval,
    coord_scaled_b_other_eval, coord_scaled_den_eval]
  norm_num [backwardLogLowerFourClosed]
  field_simp [ht0, ht1]
  ring

lemma coord_scaled_x_log_numerator_eval (z : ℝ)
    (hM : 1 - backwardMuLower z ≠ 0) :
    coordScaledXLogNumerator.eval z =
      backwardXLogUpper (backwardBlueFitRound3Back1 z) z *
        (r3Back1TReal z * (1 + r3Back1TReal z) ^ 7 *
          (1 - backwardMuLower z)) := by
  simp only [coordScaledXLogNumerator, coordScaledAdd,
    ScaledIntegerPower.eval_add, coordScaledBlueXTerm,
    coordScaledMul, ScaledIntegerPower.eval_mul,
    coordScaledMuXTerm]
  rw [coord_scaled_log_upper_five_loss_eval,
    coord_scaled_blue_fit_eval, coord_scaled_t_base_eval,
    coord_scaled_log_upper_five_loss_eval,
    coord_scaled_mu_eval, coord_scaled_den_eval]
  dsimp [backwardXLogUpper]
  field_simp [hM]

lemma coord_scaled_main_numerator_expression_eval (z : ℝ)
    (ht0 : r3Back1TReal z ≠ 0)
    (ht1 : r3Back1TReal z + 1 ≠ 0)
    (hM : 1 - backwardMuLower z ≠ 0) :
    coordScaledMainNumerator.eval z =
      (backwardBLogLowerFour (33 / 1000) (r3Back1TReal z) -
          backwardXLogUpper (backwardBlueFitRound3Back1 z) z) *
        (r3Back1TReal z * (1 + r3Back1TReal z) ^ 7 *
          (1 - backwardMuLower z)) := by
  rw [coordScaledMainNumerator, coordScaledSub,
    ScaledIntegerPower.eval_sub,
    coord_scaled_b_log_numerator_eval z ht0 ht1,
    coord_scaled_x_log_numerator_eval z hM]
  unfold backwardBLogLowerFour
  rw [backward_log_lower_below_four_closed ht0 ht1]
  ring

lemma coord_scaled_blue_numerator_target_eval (z : ℝ) :
    coordScaledBlueNumerator.eval z =
      evalPower bluePowerCoeffs z / bluePowerScale := by
  rw [ScaledIntegerPower.eval_eq_of_equivalent
    coord_scaled_blue_numerator_equivalent]
  rfl

lemma coord_scaled_main_numerator_target_eval (z : ℝ) :
    coordScaledMainNumerator.eval z =
      evalPower mainPowerCoeffs z / mainPowerScale := by
  rw [ScaledIntegerPower.eval_eq_of_equivalent
    coord_scaled_main_numerator_equivalent]
  rfl

lemma coord_scaled_blue_identity (z : ℝ)
    (hz : 1 + z ≠ 0) :
    backwardBlueRawLower (3 / 100) z -
        backwardBlueFitRound3Back1 z =
      (evalPower bluePowerCoeffs z / bluePowerScale) /
        (1 + z) := by
  apply (eq_div_iff hz).2
  rw [← coord_scaled_blue_numerator_target_eval,
    coord_scaled_blue_numerator_expression_eval z hz]

lemma coord_scaled_main_identity (z : ℝ)
    (ht0 : r3Back1TReal z ≠ 0)
    (ht1 : r3Back1TReal z + 1 ≠ 0)
    (hM : 1 - backwardMuLower z ≠ 0)
    (hden : r3Back1TReal z * (1 + r3Back1TReal z) ^ 7 *
      (1 - backwardMuLower z) ≠ 0) :
    backwardBLogLowerFour (33 / 1000) (r3Back1TReal z) -
        backwardXLogUpper (backwardBlueFitRound3Back1 z) z =
      (evalPower mainPowerCoeffs z / mainPowerScale) /
        (r3Back1TReal z * (1 + r3Back1TReal z) ^ 7 *
          (1 - backwardMuLower z)) := by
  apply (eq_div_iff hden).2
  rw [← coord_scaled_main_numerator_target_eval,
    coord_scaled_main_numerator_expression_eval z ht0 ht1 hM]

end


end BackwardCoordRound3Back1Certificate
end Arxiv2407_19026
