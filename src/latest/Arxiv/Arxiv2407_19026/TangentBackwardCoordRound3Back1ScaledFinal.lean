import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound3Back1ScaledMiddle

/-! Final scaled-integer expansions for the round-3 backward-coordinate proof. -/

namespace Arxiv2407_19026
namespace BackwardCoordRound3Back1Certificate

noncomputable section

set_option maxRecDepth 100000 in
lemma coord_scaled_b_log_numerator_from_data :
    coordScaledSub
        (coordScaledScaleBy 1 210
          (coordScaledMul coordScaledLogFourNumeratorData
            coordScaledOneMinusMuData))
        (coordScaledMul coordScaledBOtherData coordScaledDenData) =
      coordScaledBLogNumeratorData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledBLogNumeratorData,
    coordScaledBLogNumeratorDataScale,
    coordScaledBLogNumeratorDataCoefficients,
    coordScaledLogFourNumeratorData,
    coordScaledLogFourNumeratorDataScale,
    coordScaledLogFourNumeratorDataCoefficients,
    coordScaledOneMinusMuData,
    coordScaledOneMinusMuDataScale,
    coordScaledOneMinusMuDataCoefficients,
    coordScaledBOtherData,
    coordScaledBOtherDataScale, coordScaledBOtherDataCoefficients,
    coordScaledDenData,
    coordScaledDenDataScale, coordScaledDenDataCoefficients,
    coordScaledRats, coordScaledSub, coordScaledNeg,
    coordScaledAdd, coordScaledMul, coordScaledScaleBy,
    ScaledIntegerPower.sub, ScaledIntegerPower.neg,
    ScaledIntegerPower.add, ScaledIntegerPower.mul,
    ScaledIntegerPower.scaleBy, ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_b_log_numerator_expansion :
    coordScaledBLogNumerator =
      coordScaledBLogNumeratorData := by
  rw [coordScaledBLogNumerator,
    coord_scaled_log_four_numerator_expansion,
    coord_scaled_one_minus_mu_expansion,
    coord_scaled_b_other_expansion,
    coord_scaled_den_expansion]
  exact coord_scaled_b_log_numerator_from_data

set_option maxRecDepth 100000 in
lemma coord_scaled_blue_log_upper_expansion :
    coordScaledLogUpperFiveLoss coordScaledBlueFit =
      coordScaledBlueLogUpperData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledBlueLogUpperData,
    coordScaledBlueLogUpperDataScale,
    coordScaledBlueLogUpperDataCoefficients,
    coordScaledLogUpperFiveLoss, coordScaledBlueFit,
    coordScaledRats, coordScaledNeg, coordScaledComp,
    ScaledIntegerPower.neg,
    ScaledIntegerPower.comp, ScaledIntegerPower.compAux,
    ScaledIntegerPower.mul, ScaledIntegerPower.add,
    ScaledIntegerPower.constant, ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.zero,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

set_option maxRecDepth 100000 in
lemma coord_scaled_mu_log_upper_from_data :
    coordScaledLogUpperFiveLoss coordScaledMuData =
      coordScaledMuLogUpperData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledMuLogUpperData,
    coordScaledMuLogUpperDataScale,
    coordScaledMuLogUpperDataCoefficients,
    coordScaledLogUpperFiveLoss,
    coordScaledMuData, coordScaledMuDataScale,
    coordScaledMuDataCoefficients,
    coordScaledRats, coordScaledNeg, coordScaledComp,
    ScaledIntegerPower.neg,
    ScaledIntegerPower.comp, ScaledIntegerPower.compAux,
    ScaledIntegerPower.mul, ScaledIntegerPower.add,
    ScaledIntegerPower.constant, ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.zero,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_mu_log_upper_expansion :
    coordScaledLogUpperFiveLoss coordScaledMu =
      coordScaledMuLogUpperData := by
  rw [coord_scaled_mu_expansion]
  exact coord_scaled_mu_log_upper_from_data

set_option maxRecDepth 100000 in
lemma coord_scaled_blue_x_term_from_data :
    coordScaledMul coordScaledBlueLogUpperData
        coordScaledTBaseData =
      coordScaledBlueXTermData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledBlueXTermData,
    coordScaledBlueXTermDataScale,
    coordScaledBlueXTermDataCoefficients,
    coordScaledBlueLogUpperData,
    coordScaledBlueLogUpperDataScale,
    coordScaledBlueLogUpperDataCoefficients,
    coordScaledTBaseData,
    coordScaledTBaseDataScale, coordScaledTBaseDataCoefficients,
    coordScaledRats, coordScaledMul,
    ScaledIntegerPower.mul, ScaledIntegerPower.ofIntegers,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_blue_x_term_expansion :
    coordScaledBlueXTerm = coordScaledBlueXTermData := by
  rw [coordScaledBlueXTerm,
    coord_scaled_blue_log_upper_expansion,
    coord_scaled_t_base_expansion]
  exact coord_scaled_blue_x_term_from_data

set_option maxRecDepth 100000 in
lemma coord_scaled_mu_x_term_from_data :
    coordScaledMul coordScaledMuLogUpperData coordScaledDenData =
      coordScaledMuXTermData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledMuXTermData,
    coordScaledMuXTermDataScale, coordScaledMuXTermDataCoefficients,
    coordScaledMuLogUpperData,
    coordScaledMuLogUpperDataScale,
    coordScaledMuLogUpperDataCoefficients,
    coordScaledDenData,
    coordScaledDenDataScale, coordScaledDenDataCoefficients,
    coordScaledRats, coordScaledMul,
    ScaledIntegerPower.mul, ScaledIntegerPower.ofIntegers,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_mu_x_term_expansion :
    coordScaledMuXTerm = coordScaledMuXTermData := by
  rw [coordScaledMuXTerm,
    coord_scaled_mu_log_upper_expansion,
    coord_scaled_den_expansion]
  exact coord_scaled_mu_x_term_from_data

set_option maxRecDepth 100000 in
lemma coord_scaled_x_log_numerator_from_data :
    coordScaledAdd coordScaledBlueXTermData
        coordScaledMuXTermData =
      coordScaledXLogNumeratorData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledXLogNumeratorData,
    coordScaledXLogNumeratorDataScale,
    coordScaledXLogNumeratorDataCoefficients,
    coordScaledBlueXTermData,
    coordScaledBlueXTermDataScale,
    coordScaledBlueXTermDataCoefficients,
    coordScaledMuXTermData,
    coordScaledMuXTermDataScale,
    coordScaledMuXTermDataCoefficients,
    coordScaledRats, coordScaledAdd,
    ScaledIntegerPower.add, ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_x_log_numerator_expansion :
    coordScaledXLogNumerator =
      coordScaledXLogNumeratorData := by
  rw [coordScaledXLogNumerator,
    coord_scaled_blue_x_term_expansion,
    coord_scaled_mu_x_term_expansion]
  exact coord_scaled_x_log_numerator_from_data

set_option maxRecDepth 100000 in
lemma coord_scaled_blue_target_equivalent :
    ScaledIntegerPower.Equivalent
      coordScaledBlueNumeratorData coordScaledBlueTargetData := by
  norm_num (config := { maxSteps := 10000000 })
    [ScaledIntegerPower.Equivalent,
    coordScaledBlueNumeratorData,
    coordScaledBlueNumeratorDataScale,
    coordScaledBlueNumeratorDataCoefficients,
    coordScaledBlueTargetData, coordScaledRats,
    ScaledIntegerPower.ofIntegers,
    integerPowerScale, bluePowerScale, bluePowerCoeffs,
    decimalNat]

lemma coord_scaled_blue_numerator_equivalent :
    ScaledIntegerPower.Equivalent
      coordScaledBlueNumerator coordScaledBlueTargetData := by
  rw [coord_scaled_blue_numerator_expansion]
  exact coord_scaled_blue_target_equivalent

set_option maxRecDepth 100000 in
lemma coord_scaled_main_target_equivalent :
    ScaledIntegerPower.Equivalent
      (coordScaledSub coordScaledBLogNumeratorData
        coordScaledXLogNumeratorData)
      coordScaledMainNumeratorData := by
  norm_num (config := { maxSteps := 10000000 })
    [ScaledIntegerPower.Equivalent,
    coordScaledBLogNumeratorData,
    coordScaledBLogNumeratorDataScale,
    coordScaledBLogNumeratorDataCoefficients,
    coordScaledXLogNumeratorData,
    coordScaledXLogNumeratorDataScale,
    coordScaledXLogNumeratorDataCoefficients,
    coordScaledMainNumeratorData,
    coordScaledRats, coordScaledSub, coordScaledNeg,
    ScaledIntegerPower.sub, ScaledIntegerPower.neg,
    ScaledIntegerPower.add, ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerScale, integerPowerAdd,
    mainPowerScale, mainPowerCoeffs, decimalNat]

lemma coord_scaled_main_numerator_equivalent :
    ScaledIntegerPower.Equivalent
      coordScaledMainNumerator coordScaledMainNumeratorData := by
  rw [coordScaledMainNumerator,
    coord_scaled_b_log_numerator_expansion,
    coord_scaled_x_log_numerator_expansion]
  exact coord_scaled_main_target_equivalent

end

end BackwardCoordRound3Back1Certificate
end Arxiv2407_19026
