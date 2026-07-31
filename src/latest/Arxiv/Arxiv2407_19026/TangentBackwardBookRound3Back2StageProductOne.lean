import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2StageMiddle

/-! First exact product expansions for the third-round second backward book interval. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

set_option maxHeartbeats 500000 in
-- Normalizing the fourth-order blue/mu denominator product exceeds the default heartbeat budget.
set_option maxRecDepth 5000 in
-- The exact denominator coefficient lists exceed the default simplifier recursion depth.
lemma book_den_product_expansion :
    rationalPowerMul
        bookBlueDenExpandedPower bookMuDenExpandedPower =
      bookDenProductExpandedPower := by
  norm_num [decimalNat, bookBlueDenExpandedPower,
    bookMuDenExpandedPower, bookDenProductExpandedPower,
    rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

set_option maxHeartbeats 1000000 in
-- Normalizing the exact bracket/denominator Horner product exceeds the default heartbeat budget.
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
        (backwardBookBracketNumeratorFourPower
          (33 / 1000) bookTPower bookBluePower) z =
      rationalPowerEval bookBracketNumeratorExpandedPower z := by
  simp only [backwardBookBracketNumeratorFourPower,
    rationalPowerEval_add, rationalPowerEval_mul]
  rw [book_xlog_expansion, book_bracket_expansion,
    book_blue_den_expansion, book_mu_den_expansion]
  rw [← rationalPowerEval_mul
      bookBlueDenExpandedPower bookMuDenExpandedPower z,
    book_den_product_expansion]
  rw [book_bracket_product_eval]
  rw [← rationalPowerEval_add,
    book_bracket_numerator_sum_expansion]

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
