import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back2ScaledFinal

/-! Semantic bridge from the scaled-integer model to the rational model. -/

namespace Arxiv2407_19026
namespace BackwardBookRound1Back2Certificate

noncomputable section

private lemma scaled_add_eval (p q : ScaledPower) (z : ℝ) :
    (scaledAdd p q).eval z = p.eval z + q.eval z := by
  exact ScaledIntegerPower.eval_add p q z

private lemma scaled_neg_eval (p : ScaledPower) (z : ℝ) :
    (scaledNeg p).eval z = -p.eval z := by
  exact ScaledIntegerPower.eval_neg p z

private lemma scaled_sub_eval (p q : ScaledPower) (z : ℝ) :
    (scaledSub p q).eval z = p.eval z - q.eval z := by
  exact ScaledIntegerPower.eval_sub p q z

private lemma scaled_mul_eval (p q : ScaledPower) (z : ℝ) :
    (scaledMul p q).eval z = p.eval z * q.eval z := by
  exact ScaledIntegerPower.eval_mul p q z

private lemma scaled_pow_eval (p : ScaledPower) (n : ℕ) (z : ℝ) :
    (scaledPow p n).eval z = p.eval z ^ n := by
  exact ScaledIntegerPower.eval_pow p n z

private lemma scaled_scale_by_eval (numerator : ℤ)
    (denominator : ℕ) (p : ScaledPower) (z : ℝ)
    (hdenominator : denominator ≠ 0 := by norm_num) :
    (scaledScaleBy numerator denominator p hdenominator).eval z =
      (numerator / denominator) * p.eval z := by
  exact ScaledIntegerPower.eval_scaleBy
    numerator denominator hdenominator p z

private lemma scaled_comp_eval (p q : ScaledPower) (z : ℝ) :
    (scaledComp p q).eval z = p.eval (q.eval z) := by
  exact ScaledIntegerPower.eval_comp p q z

private lemma scaled_ints_eval (coefficients : List ℤ) (z : ℝ) :
    (scaledInts coefficients).eval z =
      evalIntegerPower coefficients z := by
  simp [scaledInts, ScaledIntegerPower.eval_ofIntegers]

private lemma scaled_rats_eval (scale : ℕ)
    (coefficients : List ℤ) (z : ℝ)
    (hscale : scale ≠ 0 := by norm_num) :
    (scaledRats scale coefficients hscale).eval z =
      evalIntegerPower coefficients z / scale := by
  rfl

private lemma scaled_constant_eval (numerator : ℤ)
    (denominator : ℕ) (z : ℝ)
    (hdenominator : denominator ≠ 0 := by norm_num) :
    (scaledConstant numerator denominator hdenominator).eval z =
      numerator / denominator := by
  exact ScaledIntegerPower.eval_constant
    numerator denominator hdenominator z

private lemma scaled_book_t_eval (z : ℝ) :
    scaledBookT.eval z = rationalPowerEval bookTPower z := by
  norm_num [scaledBookT, scaledRats,
    ScaledIntegerPower.eval_ofIntegers,
    bookTPower, rationalPowerComp, rationalPowerMul,
    rationalPowerShift, rationalPowerScale,
    rationalPowerAdd, evalIntegerPower, rationalPowerEval]
  ring

private lemma scaled_book_blue_eval (z : ℝ) :
    scaledBookBlue.eval z = rationalPowerEval bookBluePower z := by
  norm_num [scaledBookBlue, scaledRats,
    ScaledIntegerPower.eval_ofIntegers,
    bookBluePower, evalIntegerPower, rationalPowerEval]
  ring

private lemma scaled_taylor_nine_eval (z : ℝ) :
    scaledTaylorNine.eval z =
      rationalPowerEval backwardTaylorNinePower z := by
  norm_num [scaledTaylorNine, scaledRats,
    ScaledIntegerPower.eval_ofIntegers,
    backwardTaylorNinePower, evalIntegerPower, rationalPowerEval]
  ring

private lemma scaled_error_ten_eval (z : ℝ) :
    scaledErrorTen.eval z =
      rationalPowerEval backwardErrorTenPower z := by
  norm_num [scaledErrorTen, scaledRats,
    ScaledIntegerPower.eval_ofIntegers,
    backwardErrorTenPower, evalIntegerPower, rationalPowerEval]
  ring

private lemma scaled_mu_eval (z : ℝ) :
    scaledMu.eval z = rationalPowerEval backwardMuPower z := by
  rw [scaledMu, scaledMul, ScaledIntegerPower.eval_mul,
    scaledAdd, ScaledIntegerPower.eval_add,
    scaled_taylor_nine_eval, scaled_error_ten_eval,
    backwardMuPower, rationalPowerEval_mul,
    rationalPowerEval_add]
  norm_num [scaledInts, ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, rationalPowerEval]

private lemma scaled_log_two_numerator_eval
    (scaled : ScaledPower) (rational : RationalPowerPolynomial)
    (h : ∀ z, scaled.eval z = rationalPowerEval rational z)
    (z : ℝ) :
    (scaledLogTwoNumerator scaled).eval z =
      rationalPowerEval (backwardLogTwoNumeratorPower rational) z := by
  simp only [scaledLogTwoNumerator, scaledNeg, scaledSub, scaledMul,
    scaledAdd, scaledScaleBy, scaledPow,
    ScaledIntegerPower.eval_neg,
    ScaledIntegerPower.eval_sub, ScaledIntegerPower.eval_mul,
    ScaledIntegerPower.eval_add, ScaledIntegerPower.eval_scaleBy,
    ScaledIntegerPower.eval_pow,
    backwardLogTwoNumeratorPower,
    rationalPowerEval_neg,
    rationalPowerEval_sub, rationalPowerEval_mul,
    rationalPowerEval_add, rationalPowerEval_scale,
    rationalPowerEval_pow]
  rw [h]
  norm_num [scaledInts, ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, rationalPowerEval]

private lemma scaled_log_two_denominator_eval
    (scaled : ScaledPower) (rational : RationalPowerPolynomial)
    (h : ∀ z, scaled.eval z = rationalPowerEval rational z)
    (z : ℝ) :
    (scaledLogTwoDenominator scaled).eval z =
      rationalPowerEval (backwardLogTwoDenominatorPower rational) z := by
  simp only [scaledLogTwoDenominator, scaledSub, scaledMul,
    scaledScaleBy, scaledPow,
    ScaledIntegerPower.eval_sub, ScaledIntegerPower.eval_mul,
    ScaledIntegerPower.eval_scaleBy,
    ScaledIntegerPower.eval_pow,
    backwardLogTwoDenominatorPower,
    rationalPowerEval_sub, rationalPowerEval_mul,
    rationalPowerEval_scale,
    rationalPowerEval_pow]
  rw [h]
  norm_num [scaledInts, ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, rationalPowerEval]

private lemma scaled_log_two_denominator_rest_eval
    (scaled : ScaledPower) (rational : RationalPowerPolynomial)
    (h : ∀ z, scaled.eval z = rationalPowerEval rational z)
    (z : ℝ) :
    (scaledLogTwoDenominatorRest scaled).eval z =
      rationalPowerEval
        (rationalPowerScale 6
          (rationalPowerPow (rationalPowerSub [2] rational) 3)) z := by
  simp only [scaledLogTwoDenominatorRest, scaledSub,
    scaledScaleBy, scaledPow,
    ScaledIntegerPower.eval_sub,
    ScaledIntegerPower.eval_scaleBy,
    ScaledIntegerPower.eval_pow,
    rationalPowerEval_sub, rationalPowerEval_scale,
    rationalPowerEval_pow]
  rw [h]
  norm_num [scaledInts, ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, rationalPowerEval]

private lemma scaled_exp_lower_five_eval
    (scaled : ScaledPower) (rational : RationalPowerPolynomial)
    (h : ∀ z, scaled.eval z = rationalPowerEval rational z)
    (z : ℝ) :
    (scaledExpLowerFive scaled).eval z =
      rationalPowerEval (backwardExpLowerFivePower rational) z := by
  rw [scaledExpLowerFive, scaledComp,
    ScaledIntegerPower.eval_comp,
    backwardExpLowerFivePower, rationalPowerEval_comp,
    h]
  norm_num [scaledRats, ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, rationalPowerEval]
  ring

private lemma scaled_coord_log_upper_eval
    (scaled : ScaledPower) (rational : RationalPowerPolynomial)
    (h : ∀ z, scaled.eval z = rationalPowerEval rational z)
    (z : ℝ) :
    (scaledCoordLogUpper scaled).eval z =
      rationalPowerEval (backwardCoordLogUpperPower rational) z := by
  simp only [scaledCoordLogUpper, scaledSub, scaledScaleBy,
    scaledComp, ScaledIntegerPower.eval_sub,
    ScaledIntegerPower.eval_scaleBy,
    ScaledIntegerPower.eval_comp,
    backwardCoordLogUpperPower,
    rationalPowerEval_sub, rationalPowerEval_scale,
    rationalPowerEval_comp]
  rw [h]
  norm_num [scaledInts, scaledRats, scaledConstant,
    ScaledIntegerPower.eval_ofIntegers,
    ScaledIntegerPower.eval_constant,
    evalIntegerPower, rationalPowerEval]
  ring

private lemma scaled_log_upper_seven_eval (z : ℝ) :
    scaledLogUpperSeven.eval z =
      rationalPowerEval backwardLogUpperSevenPower z := by
  rw [scaledLogUpperSeven, scaledNeg,
    ScaledIntegerPower.eval_neg, scaledComp,
    ScaledIntegerPower.eval_comp,
    backwardLogUpperSevenPower, rationalPowerEval_neg,
    rationalPowerEval_comp]
  norm_num [scaledInts, scaledRats,
    ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, rationalPowerEval]
  ring

private lemma scaled_alog_eval (z : ℝ) :
    scaledALog.eval z =
      rationalPowerEval (backwardALogPower (2 / 25) bookTPower) z := by
  have hOneT (x : ℝ) :
      (scaledAdd (scaledInts [1]) scaledBookT).eval x =
        rationalPowerEval (rationalPowerAdd [1] bookTPower) x := by
    rw [scaled_add_eval, rationalPowerEval_add,
      scaled_ints_eval, scaled_book_t_eval]
    norm_num [evalIntegerPower, rationalPowerEval]
  simp only [scaledALog, scaled_add_eval, scaled_neg_eval,
    scaled_mul_eval, scaled_pow_eval, scaled_scale_by_eval,
    backwardALogPower, rationalPowerEval_add,
    rationalPowerEval_neg, rationalPowerEval_mul,
    rationalPowerEval_pow, rationalPowerEval_scale]
  rw [scaled_coord_log_upper_eval
      (scaledAdd (scaledInts [1]) scaledBookT)
      (rationalPowerAdd [1] bookTPower) hOneT,
    scaled_exp_lower_five_eval
      scaledBookT bookTPower scaled_book_t_eval,
    scaled_book_t_eval]
  norm_num [scaled_constant_eval, rationalPowerEval]

private lemma scaled_book_bracket_eval (z : ℝ) :
    scaledBookBracket.eval z =
      rationalPowerEval
        (backwardBookBracketPower (2 / 25) bookTPower) z := by
  rw [scaledBookBracket, scaledAdd,
    ScaledIntegerPower.eval_add, scaledNeg,
    ScaledIntegerPower.eval_neg, scaledPow,
    ScaledIntegerPower.eval_pow, scaledMul,
    ScaledIntegerPower.eval_mul, scaledSub,
    ScaledIntegerPower.eval_sub, scaled_alog_eval,
    scaled_log_upper_seven_eval,
    backwardBookBracketPower, rationalPowerEval_add,
    rationalPowerEval_neg, rationalPowerEval_pow,
    rationalPowerEval_mul, rationalPowerEval_sub]
  norm_num [scaledInts, ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, rationalPowerEval]

private lemma scaled_entropy_numerator_eval (z : ℝ) :
    scaledEntropyNumerator.eval z =
      rationalPowerEval backwardEntropyNumeratorPower z := by
  simp only [scaledEntropyNumerator, scaledScaleBy,
    scaledMul, scaledAdd, scaledPow,
    ScaledIntegerPower.eval_scaleBy,
    ScaledIntegerPower.eval_mul,
    ScaledIntegerPower.eval_add,
    ScaledIntegerPower.eval_pow,
    backwardEntropyNumeratorPower,
    rationalPowerEval_scale, rationalPowerEval_mul,
    rationalPowerEval_add, rationalPowerEval_pow]
  norm_num [scaledInts, ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, rationalPowerEval]

private lemma scaled_entropy_denominator_eval (z : ℝ) :
    scaledEntropyDenominator.eval z =
      rationalPowerEval backwardEntropyDenominatorPower z := by
  rw [scaledEntropyDenominator, scaledPow,
    ScaledIntegerPower.eval_pow,
    backwardEntropyDenominatorPower, rationalPowerEval_pow]
  norm_num [scaledInts, ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, rationalPowerEval]

private lemma scaled_ramsey_eval (z : ℝ) :
    scaledRamsey.eval z =
      rationalPowerEval (backwardRamseyPower (9 / 200)) z := by
  rw [scaledRamsey, scaledMul,
    ScaledIntegerPower.eval_mul, scaledAdd,
    ScaledIntegerPower.eval_add,
    scaled_taylor_nine_eval, scaled_error_ten_eval,
    backwardRamseyPower, rationalPowerEval_mul,
    rationalPowerEval_add]
  norm_num [scaledRats, ScaledIntegerPower.eval_ofIntegers,
    evalIntegerPower, rationalPowerEval]
  left
  ring

private lemma scaled_entropy_ramsey_eval (z : ℝ) :
    scaledEntropyRamseyNumerator.eval z =
      rationalPowerEval
        (backwardEntropyRamseyNumeratorPower (9 / 200)) z := by
  rw [scaledEntropyRamseyNumerator, scaledAdd,
    ScaledIntegerPower.eval_add, scaledMul,
    ScaledIntegerPower.eval_mul,
    scaled_entropy_numerator_eval,
    scaled_ramsey_eval, scaled_entropy_denominator_eval,
    backwardEntropyRamseyNumeratorPower,
    rationalPowerEval_add, rationalPowerEval_mul]

private lemma scaled_den_product_eval (z : ℝ) :
    scaledDenProduct.eval z =
      rationalPowerEval
          (backwardLogTwoDenominatorPower bookBluePower) z *
        rationalPowerEval
          (backwardLogTwoDenominatorPower backwardMuPower) z := by
  rw [scaledDenProduct, scaledMul,
    ScaledIntegerPower.eval_mul,
    scaled_log_two_denominator_eval
      scaledBookBlue bookBluePower scaled_book_blue_eval,
    scaled_log_two_denominator_eval
      scaledMu backwardMuPower scaled_mu_eval]

private lemma scaled_xlog_eval (z : ℝ) :
    scaledXLogNumerator.eval z =
      rationalPowerEval
        (backwardXLogNumeratorTwoPower bookBluePower) z := by
  simp only [scaledXLogNumerator,
    scaled_add_eval, scaled_mul_eval]
  rw [
    scaled_log_two_numerator_eval
      scaledBookBlue bookBluePower scaled_book_blue_eval,
    scaled_log_two_denominator_rest_eval
      scaledMu backwardMuPower scaled_mu_eval,
    scaled_log_two_numerator_eval
      scaledMu backwardMuPower scaled_mu_eval,
    scaled_log_two_denominator_eval
      scaledBookBlue bookBluePower scaled_book_blue_eval,
    backwardXLogNumeratorTwoPower,
    rationalPowerEval_add, rationalPowerEval_mul]
  simp only [rationalPowerEval_mul]

private lemma scaled_bracket_numerator_eval (z : ℝ) :
    scaledBracketNumerator.eval z =
      rationalPowerEval
        (backwardBookBracketNumeratorTwoPower
          (2 / 25) bookTPower bookBluePower) z := by
  simp only [scaledBracketNumerator,
    scaled_add_eval, scaled_mul_eval]
  rw [
    scaled_xlog_eval, scaled_book_bracket_eval,
    scaled_den_product_eval,
    backwardBookBracketNumeratorTwoPower,
    rationalPowerEval_add, rationalPowerEval_mul]
  rw [rationalPowerEval_mul]

lemma scaled_book_numerator_eval (z : ℝ) :
    scaledBookNumerator.eval z =
      rationalPowerEval
        (backwardBookNumeratorTwoPower
          (2 / 25) (9 / 200) bookTPower bookBluePower) z := by
  simp only [scaledBookNumerator, scaled_add_eval,
    scaled_mul_eval, scaled_scale_by_eval]
  rw [
    scaled_entropy_ramsey_eval, scaled_den_product_eval,
    scaled_bracket_numerator_eval,
    scaled_entropy_denominator_eval,
    backwardBookNumeratorTwoPower,
    rationalPowerEval_add, rationalPowerEval_mul,
    rationalPowerEval_scale]
  simp only [rationalPowerEval_mul]
  norm_num

lemma book_numerator_scaled_eval (z : ℝ) :
    rationalPowerEval
        (backwardBookNumeratorTwoPower
          (2 / 25) (9 / 200) bookTPower bookBluePower) z =
      evalIntegerPower bookNumeratorCoeffs z /
        bookNumeratorScale := by
  rw [← scaled_book_numerator_eval]
  have hequivalent :=
    ScaledIntegerPower.eval_eq_of_equivalent
      scaled_book_numerator_equivalent z
  rw [hequivalent]
  rfl

end

end BackwardBookRound1Back2Certificate
end Arxiv2407_19026
