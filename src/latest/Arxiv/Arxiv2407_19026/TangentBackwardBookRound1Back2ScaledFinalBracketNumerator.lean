import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back2ScaledData

/-! Exact data check for the final bracket numerator. -/

namespace Arxiv2407_19026
namespace BackwardBookRound1Back2Certificate

noncomputable section

set_option maxHeartbeats 1000000 in
-- Exact bracket/denominator integer multiplication exceeds the default budget.
set_option maxRecDepth 100000 in
lemma scaled_bracket_numerator_from_data :
    scaledAdd scaledXLogNumeratorData
        (scaledMul scaledBookBracketData scaledDenProductData) =
      scaledBracketNumeratorData := by
  norm_num (config := { maxSteps := 10000000 })
    [scaledBracketNumeratorData,
    scaledBracketNumeratorDataScale,
    scaledBracketNumeratorDataCoefficients,
    scaledXLogNumeratorData,
    scaledXLogNumeratorDataScale,
    scaledXLogNumeratorDataCoefficients,
    scaledBookBracketData,
    scaledBookBracketDataScale,
    scaledBookBracketDataCoefficients,
    scaledDenProductData, scaledDenProductDataScale,
    scaledDenProductDataCoefficients,
    scaledRats, scaledAdd, scaledMul,
    ScaledIntegerPower.mul, ScaledIntegerPower.add,
    ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

end

end BackwardBookRound1Back2Certificate
end Arxiv2407_19026
