import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound1Back1ScaledData

/-! Basic scaled-integer expansions for the round-1 backward-coordinate proof. -/

namespace Arxiv2407_19026
namespace BackwardCoordRound1Back1Certificate

noncomputable section

set_option maxRecDepth 100000 in
lemma coord_scaled_t_expansion :
    coordScaledT = coordScaledTData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledT, coordScaledTData,
    coordScaledTDataScale, coordScaledTDataCoefficients,
    coordScaledComp, coordScaledRats,
    ScaledIntegerPower.comp, ScaledIntegerPower.compAux,
    ScaledIntegerPower.mul, ScaledIntegerPower.add,
    ScaledIntegerPower.constant, ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.zero,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

set_option maxRecDepth 100000 in
lemma coord_scaled_q_expansion :
    coordScaledQ = coordScaledQData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledQ, coordScaledQData,
    coordScaledQDataScale, coordScaledQDataCoefficients,
    coordScaledNewCorrection, coordScaledTaylorNine,
    coordScaledErrorTen, coordScaledRats,
    coordScaledSub, coordScaledNeg, coordScaledMul,
    coordScaledScaleBy,
    ScaledIntegerPower.sub, ScaledIntegerPower.neg,
    ScaledIntegerPower.mul, ScaledIntegerPower.scaleBy,
    ScaledIntegerPower.add, ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

set_option maxRecDepth 100000 in
lemma coord_scaled_exp_point_three_expansion :
    coordScaledExpPointThreeLower =
      coordScaledExpPointThreeLowerData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledExpPointThreeLower,
    coordScaledExpPointThreeLowerData,
    coordScaledExpPointThreeLowerDataScale,
    coordScaledExpPointThreeLowerDataCoefficients,
    coordScaledTaylorNine, coordScaledErrorTen,
    coordScaledConstant, coordScaledRats,
    coordScaledSub, coordScaledComp,
    ScaledIntegerPower.sub, ScaledIntegerPower.neg,
    ScaledIntegerPower.comp, ScaledIntegerPower.compAux,
    ScaledIntegerPower.mul, ScaledIntegerPower.add,
    ScaledIntegerPower.constant, ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.zero,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

set_option maxRecDepth 100000 in
lemma coord_scaled_exp_series_from_q :
    coordScaledAdd
        (coordScaledAdd
          (coordScaledAdd (coordScaledInts [1])
            (coordScaledAdd coordScaledQData
              (coordScaledConstant 3 10)))
          (coordScaledScaleBy 1 2
            (coordScaledPow
              (coordScaledAdd coordScaledQData
                (coordScaledConstant 3 10)) 2)))
        (coordScaledAdd
          (coordScaledScaleBy 1 6
            (coordScaledPow
              (coordScaledAdd coordScaledQData
                (coordScaledConstant 3 10)) 3))
          (coordScaledScaleBy 1 24
            (coordScaledPow
              (coordScaledAdd coordScaledQData
                (coordScaledConstant 3 10)) 4))) =
      coordScaledExpSeriesData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledExpSeriesData,
    coordScaledExpSeriesDataScale,
    coordScaledExpSeriesDataCoefficients,
    coordScaledQData, coordScaledQDataScale,
    coordScaledQDataCoefficients,
    coordScaledInts, coordScaledRats, coordScaledConstant,
    coordScaledAdd, coordScaledPow, coordScaledScaleBy,
    ScaledIntegerPower.pow, ScaledIntegerPower.mul,
    ScaledIntegerPower.scaleBy, ScaledIntegerPower.add,
    ScaledIntegerPower.constant, ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.zero,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_exp_series_expansion :
    coordScaledExpSeries = coordScaledExpSeriesData := by
  rw [coordScaledExpSeries, coordScaledR,
    coord_scaled_q_expansion]
  exact coord_scaled_exp_series_from_q

set_option maxRecDepth 100000 in
lemma coord_scaled_exp_q_from_data :
    coordScaledMul coordScaledExpPointThreeLowerData
        coordScaledExpSeriesData =
      coordScaledExpQLowerData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledExpQLowerData,
    coordScaledExpQLowerDataScale,
    coordScaledExpQLowerDataCoefficients,
    coordScaledExpPointThreeLowerData,
    coordScaledExpPointThreeLowerDataScale,
    coordScaledExpPointThreeLowerDataCoefficients,
    coordScaledExpSeriesData,
    coordScaledExpSeriesDataScale,
    coordScaledExpSeriesDataCoefficients,
    coordScaledRats, coordScaledMul,
    ScaledIntegerPower.mul, ScaledIntegerPower.ofIntegers,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_exp_q_expansion :
    coordScaledExpQLower = coordScaledExpQLowerData := by
  rw [coordScaledExpQLower,
    coord_scaled_exp_point_three_expansion,
    coord_scaled_exp_series_expansion]
  exact coord_scaled_exp_q_from_data

set_option maxRecDepth 100000 in
lemma coord_scaled_blue_numerator_from_data :
    coordScaledSub
        (coordScaledMul coordScaledZ coordScaledExpQLowerData)
        (coordScaledMul coordScaledBlueFit
          (coordScaledInts [1, 1])) =
      coordScaledBlueNumeratorData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledBlueNumeratorData,
    coordScaledBlueNumeratorDataScale,
    coordScaledBlueNumeratorDataCoefficients,
    coordScaledExpQLowerData,
    coordScaledExpQLowerDataScale,
    coordScaledExpQLowerDataCoefficients,
    coordScaledZ, coordScaledBlueFit,
    coordScaledInts, coordScaledRats,
    coordScaledSub, coordScaledNeg, coordScaledMul,
    ScaledIntegerPower.sub, ScaledIntegerPower.neg,
    ScaledIntegerPower.mul, ScaledIntegerPower.add,
    ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_blue_numerator_expansion :
    coordScaledBlueNumerator = coordScaledBlueNumeratorData := by
  rw [coordScaledBlueNumerator,
    coord_scaled_exp_q_expansion]
  exact coord_scaled_blue_numerator_from_data

set_option maxRecDepth 100000 in
lemma coord_scaled_mu_expansion :
    coordScaledMu = coordScaledMuData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledMu, coordScaledMuData,
    coordScaledMuDataScale, coordScaledMuDataCoefficients,
    coordScaledZ, coordScaledExpLowerFive,
    coordScaledInts, coordScaledRats, coordScaledMul,
    ScaledIntegerPower.mul, ScaledIntegerPower.ofIntegers,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

set_option maxRecDepth 100000 in
lemma coord_scaled_one_minus_mu_from_data :
    coordScaledSub (coordScaledInts [1]) coordScaledMuData =
      coordScaledOneMinusMuData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledOneMinusMuData,
    coordScaledOneMinusMuDataScale,
    coordScaledOneMinusMuDataCoefficients,
    coordScaledMuData, coordScaledMuDataScale,
    coordScaledMuDataCoefficients,
    coordScaledInts, coordScaledRats, coordScaledSub,
    ScaledIntegerPower.sub, ScaledIntegerPower.neg,
    ScaledIntegerPower.add, ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_one_minus_mu_expansion :
    coordScaledOneMinusMu = coordScaledOneMinusMuData := by
  rw [coordScaledOneMinusMu, coord_scaled_mu_expansion]
  exact coord_scaled_one_minus_mu_from_data

end

end BackwardCoordRound1Back1Certificate
end Arxiv2407_19026
