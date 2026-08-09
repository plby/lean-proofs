import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back1StageBasic

/-! Analytic-component coefficient expansions for the first backward book interval. -/

namespace Arxiv2407_19026
namespace BackwardBookRound1Back1Certificate

noncomputable section

lemma book_xlog_expansion :
    backwardXLogNumeratorTwoPower bookBluePower =
      bookXLogExpandedPower := by
  rw [backwardXLogNumeratorTwoPower,
    book_blue_log_numerator_expansion,
    book_mu_den_rest_expansion,
    book_mu_log_numerator_expansion,
    book_blue_den_expansion]
  norm_num [decimalNat, bookBlueLogNumeratorPower,
    bookMuDenRestExpandedPower,
    bookMuLogNumeratorPower, bookBlueDenExpandedPower,
    bookXLogExpandedPower, rationalPowerMul,
    rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

lemma book_alog_expansion :
    backwardALogPower (2 / 25) bookTPower =
      bookALogExpandedPower := by
  rw [book_t_expansion]
  norm_num [decimalNat, backwardALogPower,
    backwardCoordLogUpperPower,
    backwardExpLowerFivePower,
    bookTExpandedPower, bookALogExpandedPower,
    rationalPowerComp, rationalPowerPow,
    rationalPowerMul, rationalPowerShift, rationalPowerScale,
    rationalPowerSub, rationalPowerNeg, rationalPowerAdd]

lemma book_bracket_expansion :
    backwardBookBracketPower (2 / 25) bookTPower =
      bookBracketExpandedPower := by
  rw [backwardBookBracketPower, book_alog_expansion]
  norm_num [decimalNat, backwardLogUpperSevenPower,
    bookALogExpandedPower, bookBracketExpandedPower,
    rationalPowerComp, rationalPowerPow,
    rationalPowerMul, rationalPowerShift, rationalPowerScale,
    rationalPowerSub, rationalPowerNeg, rationalPowerAdd]

end

end BackwardBookRound1Back1Certificate
end Arxiv2407_19026
