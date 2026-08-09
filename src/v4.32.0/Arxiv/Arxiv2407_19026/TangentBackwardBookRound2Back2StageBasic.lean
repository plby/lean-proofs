import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back2StageData

/-! Basic exact coefficient expansions for the second-round second backward book interval. -/

namespace Arxiv2407_19026
namespace BackwardBookRound2Back2Certificate

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
    backwardLogThreeNumeratorPower bookBluePower =
      bookBlueLogNumeratorPower := by
  norm_num [decimalNat, backwardLogThreeNumeratorPower, bookBluePower,
    bookBlueLogNumeratorPower, rationalPowerPow,
    rationalPowerMul, rationalPowerShift, rationalPowerScale,
    rationalPowerSub, rationalPowerNeg, rationalPowerAdd]

lemma book_blue_den_expansion :
    backwardLogThreeDenominatorPower bookBluePower =
      bookBlueDenExpandedPower := by
  norm_num [decimalNat, backwardLogThreeDenominatorPower, bookBluePower,
    bookBlueDenExpandedPower, rationalPowerPow,
    rationalPowerMul, rationalPowerShift, rationalPowerScale,
    rationalPowerSub, rationalPowerNeg, rationalPowerAdd]

lemma book_mu_log_numerator_expansion :
    backwardLogThreeNumeratorPower backwardMuPower =
      bookMuLogNumeratorPower := by
  rw [book_mu_expansion]
  norm_num [decimalNat, backwardLogThreeNumeratorPower,
    bookMuExpandedPower, bookMuLogNumeratorPower,
    rationalPowerPow, rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerSub,
    rationalPowerNeg, rationalPowerAdd]

lemma book_mu_den_rest_expansion :
    backwardLogThreeDenominatorRestPower backwardMuPower =
      bookMuDenRestExpandedPower := by
  rw [book_mu_expansion]
  norm_num [decimalNat, backwardLogThreeDenominatorRestPower,
    bookMuExpandedPower, bookMuDenRestExpandedPower, rationalPowerPow,
    rationalPowerMul, rationalPowerShift, rationalPowerScale,
    rationalPowerSub, rationalPowerNeg, rationalPowerAdd]

lemma book_mu_den_expansion :
    backwardLogThreeDenominatorPower backwardMuPower =
      bookMuDenExpandedPower := by
  rw [book_mu_expansion]
  norm_num [decimalNat, backwardLogThreeDenominatorPower,
    bookMuExpandedPower, bookMuDenExpandedPower,
    rationalPowerPow, rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerSub,
    rationalPowerNeg, rationalPowerAdd]

end

end BackwardBookRound2Back2Certificate
end Arxiv2407_19026
