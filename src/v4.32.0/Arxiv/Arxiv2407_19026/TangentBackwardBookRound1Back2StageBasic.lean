import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back2StageData

/-! Basic exact coefficient expansions for the first-round second backward book interval. -/

namespace Arxiv2407_19026
namespace BackwardBookRound1Back2Certificate

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
    backwardLogTwoNumeratorPower bookBluePower =
      bookBlueLogNumeratorPower := by
  norm_num [decimalNat, backwardLogTwoNumeratorPower, bookBluePower,
    bookBlueLogNumeratorPower, rationalPowerPow,
    rationalPowerMul, rationalPowerShift, rationalPowerScale,
    rationalPowerSub, rationalPowerNeg, rationalPowerAdd]

lemma book_blue_den_expansion :
    backwardLogTwoDenominatorPower bookBluePower =
      bookBlueDenExpandedPower := by
  norm_num [decimalNat, backwardLogTwoDenominatorPower, bookBluePower,
    bookBlueDenExpandedPower, rationalPowerPow,
    rationalPowerMul, rationalPowerShift, rationalPowerScale,
    rationalPowerSub, rationalPowerNeg, rationalPowerAdd]

lemma book_mu_log_numerator_expansion :
    backwardLogTwoNumeratorPower backwardMuPower =
      bookMuLogNumeratorPower := by
  rw [book_mu_expansion]
  norm_num [decimalNat, backwardLogTwoNumeratorPower,
    bookMuExpandedPower, bookMuLogNumeratorPower,
    rationalPowerPow, rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerSub,
    rationalPowerNeg, rationalPowerAdd]

lemma book_mu_den_rest_expansion :
    rationalPowerScale 6
        (rationalPowerPow
          (rationalPowerSub [2] backwardMuPower) 3) =
      bookMuDenRestExpandedPower := by
  rw [book_mu_expansion]
  norm_num [decimalNat, bookMuExpandedPower,
    bookMuDenRestExpandedPower, rationalPowerPow,
    rationalPowerMul, rationalPowerShift, rationalPowerScale,
    rationalPowerSub, rationalPowerNeg, rationalPowerAdd]

lemma book_mu_den_expansion :
    backwardLogTwoDenominatorPower backwardMuPower =
      bookMuDenExpandedPower := by
  rw [book_mu_expansion]
  norm_num [decimalNat, backwardLogTwoDenominatorPower,
    bookMuExpandedPower, bookMuDenExpandedPower,
    rationalPowerPow, rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerSub,
    rationalPowerNeg, rationalPowerAdd]

end

end BackwardBookRound1Back2Certificate
end Arxiv2407_19026
