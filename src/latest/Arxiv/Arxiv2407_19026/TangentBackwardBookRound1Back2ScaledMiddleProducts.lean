import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back2ScaledData

/-! Exact scaled-integer data checks for the logarithmic products. -/

namespace Arxiv2407_19026
namespace BackwardBookRound1Back2Certificate

noncomputable section

set_option maxHeartbeats 1000000 in
-- Exact integer products for the logarithmic numerator exceed the default budget.
set_option maxRecDepth 100000 in
lemma scaled_xlog_from_data :
    scaledAdd
        (scaledMul scaledBlueLogNumeratorData scaledMuDenRestData)
        (scaledMul scaledMuLogNumeratorData scaledBlueDenData) =
      scaledXLogNumeratorData := by
  norm_num (config := { maxSteps := 10000000 })
    [scaledXLogNumeratorData,
    scaledXLogNumeratorDataScale,
    scaledXLogNumeratorDataCoefficients,
    scaledBlueLogNumeratorData,
    scaledBlueLogNumeratorDataScale,
    scaledBlueLogNumeratorDataCoefficients,
    scaledMuDenRestData, scaledMuDenRestDataScale,
    scaledMuDenRestDataCoefficients,
    scaledMuLogNumeratorData,
    scaledMuLogNumeratorDataScale,
    scaledMuLogNumeratorDataCoefficients,
    scaledBlueDenData, scaledBlueDenDataScale,
    scaledBlueDenDataCoefficients,
    scaledRats, scaledAdd, scaledMul,
    ScaledIntegerPower.mul, ScaledIntegerPower.add,
    ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

set_option maxHeartbeats 1000000 in
-- Exact integer denominator multiplication exceeds the default budget.
set_option maxRecDepth 100000 in
lemma scaled_den_product_from_data :
    scaledMul scaledBlueDenData scaledMuDenData =
      scaledDenProductData := by
  norm_num (config := { maxSteps := 10000000 })
    [scaledDenProductData, scaledDenProductDataScale,
    scaledDenProductDataCoefficients,
    scaledBlueDenData, scaledBlueDenDataScale,
    scaledBlueDenDataCoefficients,
    scaledMuDenData, scaledMuDenDataScale,
    scaledMuDenDataCoefficients,
    scaledRats, scaledMul,
    ScaledIntegerPower.mul,
    ScaledIntegerPower.ofIntegers,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

end

end BackwardBookRound1Back2Certificate
end Arxiv2407_19026
