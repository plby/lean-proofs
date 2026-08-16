import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back2ScaledData

/-! Exact scaled-integer data checks for the logarithmic book bracket. -/

namespace Arxiv2407_19026
namespace BackwardBookRound1Back2Certificate

noncomputable section

set_option maxHeartbeats 1000000 in
-- Exact composition and integer coefficient normalization exceeds the default budget.
set_option maxRecDepth 100000 in
lemma scaled_alog_expansion : scaledALog = scaledALogData := by
  norm_num (config := { maxSteps := 10000000 })
    [scaledALogData, scaledALogDataScale,
    scaledALogDataCoefficients,
    scaledALog, scaledCoordLogUpper,
    scaledExpLowerFive, scaledBookT,
    scaledInts, scaledRats, scaledConstant,
    scaledAdd, scaledNeg, scaledSub, scaledMul,
    scaledPow, scaledComp, scaledScaleBy,
    ScaledIntegerPower.comp,
    ScaledIntegerPower.compAux,
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
-- Exact integer coefficient normalization exceeds the default budget.
set_option maxRecDepth 100000 in
lemma scaled_book_bracket_from_data :
    scaledAdd (scaledNeg (scaledPow (scaledInts [0, 1]) 2))
        (scaledMul (scaledInts [0, 1])
          (scaledSub scaledALogData scaledLogUpperSeven)) =
      scaledBookBracketData := by
  norm_num (config := { maxSteps := 10000000 })
    [scaledBookBracketData,
    scaledBookBracketDataScale,
    scaledBookBracketDataCoefficients,
    scaledALogData, scaledALogDataScale,
    scaledALogDataCoefficients,
    scaledLogUpperSeven, scaledInts, scaledRats,
    scaledAdd, scaledNeg, scaledSub,
    scaledMul, scaledPow, scaledComp,
    ScaledIntegerPower.comp,
    ScaledIntegerPower.compAux,
    ScaledIntegerPower.pow, ScaledIntegerPower.mul,
    ScaledIntegerPower.sub, ScaledIntegerPower.neg,
    ScaledIntegerPower.add, ScaledIntegerPower.constant,
    ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.zero,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

end

end BackwardBookRound1Back2Certificate
end Arxiv2407_19026
