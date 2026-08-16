import Arxiv.Arxiv2407_19026.NumericalProfilesBook3PowerStages

/-! Semantic evaluation of the staged third-profile book polynomial. -/

namespace Arxiv2407_19026
namespace NumericalProfilesBook3Certificate

noncomputable section

lemma eval_book_three_v_power (z : ℝ) :
    rationalPowerEval bookThreeVPower z = beta0VLarge z := by
  simp [bookThreeVPower, beta0VLarge,
    rationalPowerEval_add, rationalPowerEval_scale,
    rationalPowerEval_pow, rationalPowerEval]
  ring

lemma eval_book_three_x_power (z : ℝ) :
    rationalPowerEval bookThreeXPower z =
      1 - z * beta0VLarge z := by
  simp [bookThreeXPower, eval_book_three_v_power,
    rationalPowerEval_sub, rationalPowerEval_mul,
    rationalPowerEval]

lemma eval_book_three_w_power (z : ℝ) :
    rationalPowerEval bookThreeWPower z =
      beta0VLarge z - 1 / 100000 := by
  simp [bookThreeWPower, eval_book_three_v_power,
    rationalPowerEval_sub, rationalPowerEval]

lemma eval_book_three_exp_neg_upper_power (z : ℝ) :
    rationalPowerEval bookThreeExpNegUpperPower z =
      expNegUpper z := by
  norm_num [bookThreeExpNegUpperPower, expNegUpper,
    KernelBounds.expNegTaylor9, KernelBounds.expNegError10,
    rationalPowerEval, Nat.factorial]
  ring_nf

lemma eval_book_three_correction_power (z : ℝ) :
    rationalPowerEval bookThreeCorrectionPower z =
      beta0CorrectionLower z := by
  simp only [bookThreeCorrectionPower, rationalPowerEval_mul,
    eval_book_three_exp_neg_upper_power]
  rw [beta0CorrectionLower]
  apply congrArg (fun p : ℝ => p * expNegUpper z)
  norm_num [rationalPowerEval]
  ring_nf

lemma eval_book_three_entropy_numerator_power (z : ℝ) :
    rationalPowerEval bookThreeEntropyNumeratorPower z =
      2 * (105 * z * (z + 2) ^ 6 +
        35 * z ^ 3 * (z + 2) ^ 4 +
        21 * z ^ 5 * (z + 2) ^ 2 +
        15 * z ^ 7) := by
  simp [bookThreeEntropyNumeratorPower,
    rationalPowerEval_add, rationalPowerEval_scale,
    rationalPowerEval_mul, rationalPowerEval_pow,
    rationalPowerEval]
  ring

lemma eval_book_three_below_numerator_power (z : ℝ) :
    rationalPowerEval bookThreeBelowNumeratorPower z =
      let X := 1 - z * beta0VLarge z
      let t := 1 - X
      (-2) *
        (28 * X *
            (15 * t * (X + 1) ^ 4 +
              5 * t ^ 3 * (X + 1) ^ 2 +
              3 * t ^ 5) +
          15 * t ^ 7) := by
  simp [bookThreeBelowNumeratorPower,
    eval_book_three_x_power, rationalPowerEval_add,
    rationalPowerEval_sub, rationalPowerEval_scale,
    rationalPowerEval_mul, rationalPowerEval_pow,
    rationalPowerEval]
  ring

lemma eval_book_three_above_numerator_power (z : ℝ) :
    rationalPowerEval bookThreeAboveNumeratorPower z =
      let W := beta0VLarge z - 1 / 100000
      let t := W - 1
      2 *
        (200 * W *
            (3 * t * (W + 1) ^ 2 + t ^ 3) -
          21 * t ^ 4 * (W + 1)) := by
  simp [bookThreeAboveNumeratorPower,
    eval_book_three_w_power, rationalPowerEval_add,
    rationalPowerEval_sub, rationalPowerEval_scale,
    rationalPowerEval_mul, rationalPowerEval_pow,
    rationalPowerEval]
  ring

lemma eval_book_three_b_one_power (z : ℝ) :
    rationalPowerEval bookThreeBOnePower z =
      105 * (z + 2) ^ 7 := by
  simp [bookThreeBOnePower, rationalPowerEval_scale,
    rationalPowerEval_pow, rationalPowerEval]
  ring

lemma eval_book_three_bx_power (z : ℝ) :
    rationalPowerEval bookThreeBXPower z =
      let X := 1 - z * beta0VLarge z
      420 * X * (X + 1) ^ 5 := by
  simp [bookThreeBXPower, eval_book_three_x_power,
    rationalPowerEval_add, rationalPowerEval_scale,
    rationalPowerEval_mul, rationalPowerEval_pow,
    rationalPowerEval]
  ring

lemma eval_book_three_bv_power (z : ℝ) :
    rationalPowerEval bookThreeBVPower z =
      let W := beta0VLarge z - 1 / 100000
      600 * W * (W + 1) ^ 3 := by
  simp [bookThreeBVPower, eval_book_three_w_power,
    rationalPowerEval_add, rationalPowerEval_scale,
    rationalPowerEval_mul, rationalPowerEval_pow,
    rationalPowerEval]
  ring

lemma eval_book_three_cleared_power (z : ℝ) :
    rationalPowerEval bookThreeClearedPower z =
      bookThreeCleared z := by
  simp only [bookThreeClearedPower, bookThreeEntropyTermPower,
    bookThreeCorrectionTermPower, bookThreeBelowTermPower,
    bookThreeZSquareTermPower, bookThreeAboveTermPower,
    eval_book_three_entropy_numerator_power,
    eval_book_three_correction_power,
    eval_book_three_below_numerator_power,
    eval_book_three_above_numerator_power,
    eval_book_three_b_one_power, eval_book_three_bx_power,
    eval_book_three_bv_power, rationalPowerEval_add,
    rationalPowerEval_neg, rationalPowerEval_scale,
    rationalPowerEval_mul, rationalPowerEval]
  dsimp [bookThreeCleared]
  norm_num [decimalNat]
  ring

lemma book_three_cleared_eq_power (z : ℝ) :
    bookThreeCleared z =
      bookThreePower bookThreePowerCoeffs z := by
  have h := congrArg (fun p => rationalPowerEval p z)
    book_three_cleared_power_integer
  rw [eval_book_three_cleared_power,
    rationalPowerEval_fromIntegers 1 bookThreePowerCoeffs z
      (by norm_num)] at h
  simpa [bookThreePower] using h


end

end NumericalProfilesBook3Certificate
end Arxiv2407_19026
