import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back2ScaledData

/-! Exact scaled-integer expansions involving the blue-coordinate polynomial. -/

namespace Arxiv2407_19026
namespace BackwardBookRound2Back2Certificate

noncomputable section

set_option maxHeartbeats 1000000 in
-- Exact fourth-order integer coefficient normalization exceeds the default budget.
set_option maxRecDepth 100000 in
lemma scaled_blue_log_numerator_expansion :
    scaledLogThreeNumerator scaledBookBlue =
      scaledBlueLogNumeratorData := by
  norm_num (config := { maxSteps := 10000000 })
    [scaledBlueLogNumeratorData,
    scaledBlueLogNumeratorDataScale,
    scaledBlueLogNumeratorDataCoefficients,
    scaledLogThreeNumerator, scaledBookBlue,
    scaledInts, scaledRats, scaledAdd,
    scaledSub, scaledMul, scaledPow, scaledScaleBy,
    ScaledIntegerPower.pow, ScaledIntegerPower.mul,
    ScaledIntegerPower.scaleBy, ScaledIntegerPower.sub,
    ScaledIntegerPower.neg, ScaledIntegerPower.add,
    ScaledIntegerPower.constant,
    ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.zero,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

set_option maxHeartbeats 1000000 in
-- Exact fourth-order integer coefficient normalization exceeds the default budget.
set_option maxRecDepth 100000 in
lemma scaled_blue_den_expansion :
    scaledLogThreeDenominator scaledBookBlue =
      scaledBlueDenData := by
  norm_num (config := { maxSteps := 10000000 })
    [scaledBlueDenData, scaledBlueDenDataScale,
    scaledBlueDenDataCoefficients,
    scaledLogThreeDenominator, scaledBookBlue,
    scaledInts, scaledRats, scaledAdd,
    scaledSub, scaledMul, scaledPow, scaledScaleBy,
    ScaledIntegerPower.pow, ScaledIntegerPower.mul,
    ScaledIntegerPower.scaleBy, ScaledIntegerPower.sub,
    ScaledIntegerPower.neg, ScaledIntegerPower.add,
    ScaledIntegerPower.constant,
    ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.zero,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

end

end BackwardBookRound2Back2Certificate
end Arxiv2407_19026
