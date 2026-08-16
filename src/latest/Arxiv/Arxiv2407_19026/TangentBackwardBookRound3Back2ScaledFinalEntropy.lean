import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2ScaledData

/-! Exact data checks for the entropy/Ramsey products. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

set_option maxHeartbeats 1000000 in
-- Exact entropy/Ramsey integer normalization exceeds the default budget.
set_option maxRecDepth 100000 in
lemma scaled_entropy_ramsey_expansion :
    scaledEntropyRamseyNumerator =
      scaledEntropyRamseyNumeratorData := by
  norm_num (config := { maxSteps := 10000000 })
    [scaledEntropyRamseyNumeratorData,
    scaledEntropyRamseyNumeratorDataScale,
    scaledEntropyRamseyNumeratorDataCoefficients,
    scaledEntropyRamseyNumerator,
    scaledEntropyNumerator, scaledEntropyDenominator,
    scaledRamsey, scaledTaylorNine, scaledErrorTen,
    scaledInts, scaledRats, scaledAdd,
    scaledMul, scaledPow, scaledScaleBy,
    ScaledIntegerPower.pow, ScaledIntegerPower.mul,
    ScaledIntegerPower.scaleBy, ScaledIntegerPower.add,
    ScaledIntegerPower.constant,
    ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.zero,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

set_option maxHeartbeats 1000000 in
-- Exact entropy/denominator integer multiplication exceeds the default budget.
set_option maxRecDepth 100000 in
lemma scaled_entropy_product_from_data :
    scaledMul scaledEntropyRamseyNumeratorData scaledDenProductData =
      scaledEntropyProductData := by
  norm_num (config := { maxSteps := 10000000 })
    [scaledEntropyProductData,
    scaledEntropyProductDataScale,
    scaledEntropyProductDataCoefficients,
    scaledEntropyRamseyNumeratorData,
    scaledEntropyRamseyNumeratorDataScale,
    scaledEntropyRamseyNumeratorDataCoefficients,
    scaledDenProductData, scaledDenProductDataScale,
    scaledDenProductDataCoefficients,
    scaledRats, scaledMul,
    ScaledIntegerPower.mul,
    ScaledIntegerPower.ofIntegers,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
