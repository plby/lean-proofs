import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2StageBasic

/-! Middle exact coefficient expansions for the third-round second backward book interval. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

set_option maxHeartbeats 1000000 in
-- Normalizing the fourth-order logarithm products exceeds the default heartbeat budget.
set_option maxRecDepth 5000 in
-- The corresponding exact coefficient lists exceed the default simplifier recursion depth.
lemma book_xlog_expansion :
    backwardXLogNumeratorFourPower bookBluePower =
      bookXLogExpandedPower := by
  rw [backwardXLogNumeratorFourPower,
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
    backwardALogPower (33 / 1000) bookTPower =
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
    backwardBookBracketPower (33 / 1000) bookTPower =
      bookBracketExpandedPower := by
  rw [backwardBookBracketPower, book_alog_expansion]
  norm_num [decimalNat, backwardLogUpperSevenPower,
    bookALogExpandedPower, bookBracketExpandedPower,
    rationalPowerComp, rationalPowerPow,
    rationalPowerMul, rationalPowerShift, rationalPowerScale,
    rationalPowerSub, rationalPowerNeg, rationalPowerAdd]

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
