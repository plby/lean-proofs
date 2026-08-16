import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back1StageMiddle

/-! Entropy branch for the round-2 first backward-book expansion. -/

namespace Arxiv2407_19026
namespace BackwardBookRound2Back1Certificate

noncomputable section

lemma book_entropy_ramsey_expansion :
    backwardEntropyRamseyNumeratorPower (33 / 1000) =
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

end BackwardBookRound2Back1Certificate
end Arxiv2407_19026
