import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back2ScaledFinalBracketProduct

/-! Exact data check for the final bracket numerator. -/

namespace Arxiv2407_19026
namespace BackwardBookRound2Back2Certificate

noncomputable section

set_option maxRecDepth 100000 in
lemma scaled_bracket_numerator_from_data :
    scaledAdd scaledXLogNumeratorData
        (scaledMul scaledBookBracketData scaledDenProductData) =
      scaledBracketNumeratorData := by
  rw [scaled_bracket_den_product_from_data]
  norm_num (config := { maxSteps := 10000000 })
    [scaledBracketNumeratorData,
    scaledBracketNumeratorDataScale,
    scaledBracketNumeratorDataCoefficients,
    scaledXLogNumeratorData,
    scaledXLogNumeratorDataScale,
    scaledXLogNumeratorDataCoefficients,
    scaledBracketDenProductData,
    scaledBracketDenProductDataScale,
    scaledBracketDenProductDataCoefficients,
    scaledRats, scaledAdd,
    ScaledIntegerPower.add,
    ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerScale, integerPowerAdd, decimalNat]

end

end BackwardBookRound2Back2Certificate
end Arxiv2407_19026
