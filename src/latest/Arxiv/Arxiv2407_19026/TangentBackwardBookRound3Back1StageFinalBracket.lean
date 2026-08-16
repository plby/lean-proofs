import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back1StageMiddle
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back1BracketIntegerData

/-! Bracket branch for the round-3 first backward-book expansion. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back1Certificate

noncomputable section

lemma book_den_product_expansion :
    rationalPowerMul
        bookBlueDenExpandedPower bookMuDenExpandedPower =
      bookDenProductExpandedPower := by
  norm_num [decimalNat, bookBlueDenExpandedPower,
    bookMuDenExpandedPower, bookDenProductExpandedPower,
    rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

lemma book_bracket_product_eval (z : ℝ) :
    rationalPowerEval bookBracketExpandedPower z *
        rationalPowerEval bookDenProductExpandedPower z =
      rationalPowerEval bookBracketProductExpandedPower z := by
  rw [← book_bracket_from_integers,
    ← book_den_product_from_integers,
    ← book_bracket_product_from_integers]
  rw [rationalPowerEval_fromIntegers,
    rationalPowerEval_fromIntegers,
    rationalPowerEval_fromIntegers]
  · have heval :
        evalIntegerPower bookBracketProductIntegerCoeffs z =
          evalIntegerPower bookBracketIntegerCoeffs z *
            evalIntegerPower bookDenProductIntegerCoeffs z := by
      rw [← book_bracket_integer_product, evalIntegerPower_mul]
    rw [heval, book_bracket_integer_scale_product]
    push_cast
    ring
  all_goals
    norm_num [bookBracketIntegerScale,
      bookDenProductIntegerScale,
      bookBracketProductIntegerScale, decimalNat]

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
          (33 / 1000) bookTPower bookBluePower) z =
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


end

end BackwardBookRound3Back1Certificate
end Arxiv2407_19026
