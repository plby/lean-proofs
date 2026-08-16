import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back1StageMiddle

/-! Entropy branch for the round-3 first backward-book expansion. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back1Certificate

noncomputable section

lemma book_entropy_ramsey_expansion :
    backwardEntropyRamseyNumeratorPower (3 / 100) =
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


end

end BackwardBookRound3Back1Certificate
end Arxiv2407_19026
