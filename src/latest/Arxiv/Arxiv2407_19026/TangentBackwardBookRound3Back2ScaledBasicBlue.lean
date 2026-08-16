import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2ScaledData

/-! Exact scaled-integer expansions involving the blue-coordinate polynomial. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

set_option maxHeartbeats 1000000 in
-- Exact fourth-order integer coefficient normalization exceeds the default budget.
set_option maxRecDepth 100000 in
lemma scaled_blue_log_numerator_expansion :
    scaledLogFourNumerator scaledBookBlue =
      scaledBlueLogNumeratorData := by
  norm_num (config := { maxSteps := 10000000 })
    [scaledBlueLogNumeratorData,
    scaledBlueLogNumeratorDataScale,
    scaledBlueLogNumeratorDataCoefficients,
    scaledLogFourNumerator, scaledBookBlue,
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
    scaledLogFourDenominator scaledBookBlue =
      scaledBlueDenData := by
  norm_num (config := { maxSteps := 10000000 })
    [scaledBlueDenData, scaledBlueDenDataScale,
    scaledBlueDenDataCoefficients,
    scaledLogFourDenominator, scaledBookBlue,
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


end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
