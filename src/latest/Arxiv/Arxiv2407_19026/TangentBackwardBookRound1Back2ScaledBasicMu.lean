import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back2ScaledData

/-! Exact scaled-integer expansions involving the auxiliary `mu` polynomial. -/

namespace Arxiv2407_19026
namespace BackwardBookRound1Back2Certificate

noncomputable section

set_option maxRecDepth 1000000 in
-- Definitional reduction of the degree-10 integer list needs a deeper stack.
lemma scaled_mu_expansion : scaledMu = scaledMuData := by
  rfl

set_option maxHeartbeats 1000000 in
-- Exact fourth-order integer coefficient normalization exceeds the default budget.
set_option maxRecDepth 100000 in
lemma scaled_mu_log_numerator_expansion :
    scaledLogTwoNumerator scaledMuData =
      scaledMuLogNumeratorData := by
  norm_num (config := { maxSteps := 10000000 })
    [scaledMuLogNumeratorData,
    scaledMuLogNumeratorDataScale,
    scaledMuLogNumeratorDataCoefficients,
    scaledLogTwoNumerator, scaledMuData,
    scaledMuDataScale, scaledMuDataCoefficients,
    scaledInts, scaledRats, scaledAdd, scaledNeg,
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
lemma scaled_mu_den_rest_expansion :
    scaledLogTwoDenominatorRest scaledMuData =
      scaledMuDenRestData := by
  norm_num (config := { maxSteps := 10000000 })
    [scaledMuDenRestData, scaledMuDenRestDataScale,
    scaledMuDenRestDataCoefficients,
    scaledLogTwoDenominatorRest, scaledMuData,
    scaledMuDataScale, scaledMuDataCoefficients,
    scaledInts, scaledRats,
    scaledSub, scaledPow, scaledScaleBy,
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
lemma scaled_mu_den_expansion :
    scaledLogTwoDenominator scaledMuData =
      scaledMuDenData := by
  norm_num (config := { maxSteps := 10000000 })
    [scaledMuDenData, scaledMuDenDataScale,
    scaledMuDenDataCoefficients,
    scaledLogTwoDenominator, scaledMuData,
    scaledMuDataScale, scaledMuDataCoefficients,
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

end BackwardBookRound1Back2Certificate
end Arxiv2407_19026
