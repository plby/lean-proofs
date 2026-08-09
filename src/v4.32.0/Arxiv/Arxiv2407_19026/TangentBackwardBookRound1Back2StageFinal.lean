import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back2StageMiddle

/-! Final exact coefficient expansions for the first-round second backward book interval. -/

namespace Arxiv2407_19026
namespace BackwardBookRound1Back2Certificate

noncomputable section

lemma book_den_product_expansion :
    rationalPowerMul
        bookBlueDenExpandedPower bookMuDenExpandedPower =
      bookDenProductExpandedPower := by
  norm_num [decimalNat, bookBlueDenExpandedPower,
    bookMuDenExpandedPower, bookDenProductExpandedPower,
    rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

set_option maxHeartbeats 500000 in
-- Normalizing the exact degree-101 Horner product exceeds the default heartbeat budget.
set_option maxRecDepth 5000 in
-- The nested Horner expression also exceeds the default recursion depth.
lemma book_bracket_product_eval (z : ℝ) :
    rationalPowerEval bookBracketExpandedPower z *
        rationalPowerEval bookDenProductExpandedPower z =
      rationalPowerEval bookBracketProductExpandedPower z := by
  norm_num [decimalNat, bookBracketExpandedPower,
    bookDenProductExpandedPower,
    bookBracketProductExpandedPower,
    rationalPowerEval]
  ring

lemma book_bracket_numerator_sum_expansion :
    rationalPowerAdd
        bookXLogExpandedPower bookBracketProductExpandedPower =
      bookBracketNumeratorExpandedPower := by
  norm_num [decimalNat, bookXLogExpandedPower,
    bookBracketProductExpandedPower,
    bookBracketNumeratorExpandedPower, rationalPowerAdd]

lemma book_bracket_numerator_eval (z : ℝ) :
    rationalPowerEval
        (backwardBookBracketNumeratorTwoPower
          (2 / 25) bookTPower bookBluePower) z =
      rationalPowerEval bookBracketNumeratorExpandedPower z := by
  simp only [backwardBookBracketNumeratorTwoPower,
    rationalPowerEval_add, rationalPowerEval_mul]
  rw [book_xlog_expansion, book_bracket_expansion,
    book_blue_den_expansion, book_mu_den_expansion]
  rw [← rationalPowerEval_mul
      bookBlueDenExpandedPower bookMuDenExpandedPower z,
    book_den_product_expansion]
  rw [book_bracket_product_eval]
  rw [← rationalPowerEval_add,
    book_bracket_numerator_sum_expansion]

lemma book_entropy_ramsey_expansion :
    backwardEntropyRamseyNumeratorPower (9 / 200) =
      bookEntropyRamseyExpandedPower := by
  norm_num [decimalNat, backwardEntropyRamseyNumeratorPower,
    backwardEntropyNumeratorPower,
    backwardEntropyDenominatorPower,
    backwardRamseyPower, backwardTaylorNinePower,
    backwardErrorTenPower,
    bookEntropyRamseyExpandedPower,
    rationalPowerPow, rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

lemma book_entropy_product_expansion :
    rationalPowerMul
        bookEntropyRamseyExpandedPower
        bookDenProductExpandedPower =
      bookEntropyProductExpandedPower := by
  norm_num [decimalNat, bookEntropyRamseyExpandedPower,
    bookDenProductExpandedPower,
    bookEntropyProductExpandedPower,
    rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

set_option maxHeartbeats 500000 in
-- Normalizing the exact degree-110 Horner product exceeds the default heartbeat budget.
set_option maxRecDepth 5000 in
-- The nested Horner expression also exceeds the default recursion depth.
lemma book_bracket_entropy_product_eval (z : ℝ) :
    rationalPowerEval bookBracketNumeratorExpandedPower z *
        rationalPowerEval backwardEntropyDenominatorPower z =
      rationalPowerEval
        bookBracketEntropyProductExpandedPower z := by
  norm_num [decimalNat, bookBracketNumeratorExpandedPower,
    backwardEntropyDenominatorPower,
    bookBracketEntropyProductExpandedPower,
    rationalPowerPow, rationalPowerMul,
    rationalPowerShift, rationalPowerScale,
    rationalPowerAdd, rationalPowerEval]
  ring

lemma book_numerator_sum_expansion :
    rationalPowerAdd bookEntropyProductExpandedPower
        (rationalPowerScale (1 / 2)
          bookBracketEntropyProductExpandedPower) =
      bookNumeratorExpandedPower := by
  norm_num [decimalNat, bookEntropyProductExpandedPower,
    bookBracketEntropyProductExpandedPower,
    bookNumeratorExpandedPower,
    rationalPowerScale, rationalPowerAdd]

lemma book_numerator_eval (z : ℝ) :
    rationalPowerEval
        (backwardBookNumeratorTwoPower
          (2 / 25) (9 / 200) bookTPower bookBluePower) z =
      rationalPowerEval bookNumeratorExpandedPower z := by
  simp only [backwardBookNumeratorTwoPower,
    rationalPowerEval_add, rationalPowerEval_mul,
    rationalPowerEval_scale]
  rw [book_entropy_ramsey_expansion,
    book_blue_den_expansion, book_mu_den_expansion]
  rw [← rationalPowerEval_mul
      bookBlueDenExpandedPower bookMuDenExpandedPower z,
    book_den_product_expansion,
    ← rationalPowerEval_mul
      bookEntropyRamseyExpandedPower
        bookDenProductExpandedPower z,
    book_entropy_product_expansion,
    book_bracket_numerator_eval,
    book_bracket_entropy_product_eval]
  rw [← rationalPowerEval_scale,
    ← rationalPowerEval_add,
    book_numerator_sum_expansion]

end

end BackwardBookRound1Back2Certificate
end Arxiv2407_19026
