import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2ScaledData

/-! Exact data check for the final bracket/entropy product. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

set_option maxHeartbeats 1000000 in
-- Exact bracket/entropy integer multiplication exceeds the default budget.
set_option maxRecDepth 100000 in
lemma scaled_bracket_entropy_product_from_data :
    scaledMul scaledBracketNumeratorData scaledEntropyDenominator =
      scaledBracketEntropyProductData := by
  norm_num (config := { maxSteps := 10000000 })
    [scaledBracketEntropyProductData,
    scaledBracketEntropyProductDataScale,
    scaledBracketEntropyProductDataCoefficients,
    scaledBracketNumeratorData,
    scaledBracketNumeratorDataScale,
    scaledBracketNumeratorDataCoefficients,
    scaledEntropyDenominator, scaledInts,
    scaledRats, scaledMul, scaledPow,
    ScaledIntegerPower.pow, ScaledIntegerPower.mul,
    ScaledIntegerPower.constant,
    ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.zero,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
