import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2StageData

/-! Basic exact coefficient expansions for the third-round second backward book interval. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

lemma book_t_expansion :
    bookTPower = bookTExpandedPower := by
  norm_num [decimalNat, bookTPower, bookTExpandedPower,
    rationalPowerComp, rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

lemma book_mu_expansion :
    backwardMuPower = bookMuExpandedPower := by
  norm_num [decimalNat, backwardMuPower, backwardTaylorNinePower,
    backwardErrorTenPower, bookMuExpandedPower,
    rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

lemma book_blue_log_numerator_expansion :
    backwardLogFourNumeratorPower bookBluePower =
      bookBlueLogNumeratorPower := by
  norm_num [decimalNat, backwardLogFourNumeratorPower, bookBluePower,
    bookBlueLogNumeratorPower, rationalPowerPow,
    rationalPowerMul, rationalPowerShift, rationalPowerScale,
    rationalPowerSub, rationalPowerNeg, rationalPowerAdd]

lemma book_blue_den_expansion :
    backwardLogFourDenominatorPower bookBluePower =
      bookBlueDenExpandedPower := by
  norm_num [decimalNat, backwardLogFourDenominatorPower, bookBluePower,
    bookBlueDenExpandedPower, rationalPowerPow,
    rationalPowerMul, rationalPowerShift, rationalPowerScale,
    rationalPowerSub, rationalPowerNeg, rationalPowerAdd]

set_option maxHeartbeats 500000 in
-- Expanding the fourth-order logarithm of the degree-10 mu polynomial exceeds the default heartbeat budget.
lemma book_mu_log_numerator_expansion :
    backwardLogFourNumeratorPower backwardMuPower =
      bookMuLogNumeratorPower := by
  rw [book_mu_expansion]
  norm_num [decimalNat, backwardLogFourNumeratorPower,
    bookMuExpandedPower, bookMuLogNumeratorPower,
    rationalPowerPow, rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerSub,
    rationalPowerNeg, rationalPowerAdd]

lemma book_mu_den_rest_expansion :
    backwardLogFourDenominatorRestPower backwardMuPower =
      bookMuDenRestExpandedPower := by
  rw [book_mu_expansion]
  norm_num [decimalNat, backwardLogFourDenominatorRestPower,
    bookMuExpandedPower, bookMuDenRestExpandedPower, rationalPowerPow,
    rationalPowerMul, rationalPowerShift, rationalPowerScale,
    rationalPowerSub, rationalPowerNeg, rationalPowerAdd]

lemma book_mu_den_expansion :
    backwardLogFourDenominatorPower backwardMuPower =
      bookMuDenExpandedPower := by
  rw [book_mu_expansion]
  norm_num [decimalNat, backwardLogFourDenominatorPower,
    bookMuExpandedPower, bookMuDenExpandedPower,
    rationalPowerPow, rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerSub,
    rationalPowerNeg, rationalPowerAdd]

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
