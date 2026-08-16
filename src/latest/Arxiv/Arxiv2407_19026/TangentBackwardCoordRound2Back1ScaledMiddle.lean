import Arxiv.Arxiv2407_19026.TangentBackwardCoordRound2Back1ScaledBasic

/-! Middle scaled-integer expansions for the round-2 backward-coordinate proof. -/

namespace Arxiv2407_19026
namespace BackwardCoordRound2Back1Certificate

noncomputable section

set_option maxRecDepth 100000 in
lemma coord_scaled_t_base_from_data :
    coordScaledMul coordScaledTData
        (coordScaledPow
          (coordScaledAdd (coordScaledInts [1]) coordScaledTData) 7) =
      coordScaledTBaseData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledTBaseData,
    coordScaledTBaseDataScale, coordScaledTBaseDataCoefficients,
    coordScaledTData, coordScaledTDataScale,
    coordScaledTDataCoefficients,
    coordScaledInts, coordScaledRats,
    coordScaledAdd, coordScaledMul, coordScaledPow,
    ScaledIntegerPower.pow, ScaledIntegerPower.mul,
    ScaledIntegerPower.add, ScaledIntegerPower.constant,
    ScaledIntegerPower.ofIntegers, ScaledIntegerPower.zero,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_t_base_expansion :
    coordScaledTBase = coordScaledTBaseData := by
  rw [coordScaledTBase, coord_scaled_t_expansion]
  exact coord_scaled_t_base_from_data

set_option maxRecDepth 100000 in
lemma coord_scaled_den_from_data :
    coordScaledMul coordScaledTBaseData
        coordScaledOneMinusMuData =
      coordScaledDenData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledDenData,
    coordScaledDenDataScale, coordScaledDenDataCoefficients,
    coordScaledTBaseData,
    coordScaledTBaseDataScale, coordScaledTBaseDataCoefficients,
    coordScaledOneMinusMuData,
    coordScaledOneMinusMuDataScale,
    coordScaledOneMinusMuDataCoefficients,
    coordScaledRats, coordScaledMul,
    ScaledIntegerPower.mul, ScaledIntegerPower.ofIntegers,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_den_expansion :
    coordScaledDen = coordScaledDenData := by
  rw [coordScaledDen, coord_scaled_t_base_expansion,
    coord_scaled_one_minus_mu_expansion]
  exact coord_scaled_den_from_data

set_option maxRecDepth 100000 in
lemma coord_scaled_log_four_numerator_from_t :
    (let t := coordScaledTData
     coordScaledMul (coordScaledSub t (coordScaledInts [1]))
       (coordScaledAdd
          (coordScaledAdd
            (coordScaledAdd
              (coordScaledAdd
                (coordScaledScaleBy 105 1 (coordScaledPow t 8))
                (coordScaledScaleBy (-136) 1 (coordScaledPow t 7)))
              (coordScaledAdd
                (coordScaledScaleBy 5212 1 (coordScaledPow t 6))
                (coordScaledScaleBy 1096 1 (coordScaledPow t 5))))
            (coordScaledAdd
              (coordScaledScaleBy 14326 1 (coordScaledPow t 4))
              (coordScaledScaleBy 1096 1 (coordScaledPow t 3))))
          (coordScaledAdd
            (coordScaledAdd
              (coordScaledScaleBy 5212 1 (coordScaledPow t 2))
              (coordScaledScaleBy (-136) 1 t))
            (coordScaledInts [105])))) =
      coordScaledLogFourNumeratorData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledLogFourNumeratorData,
    coordScaledLogFourNumeratorDataScale,
    coordScaledLogFourNumeratorDataCoefficients,
    coordScaledTData, coordScaledTDataScale,
    coordScaledTDataCoefficients,
    coordScaledInts, coordScaledRats,
    coordScaledSub, coordScaledNeg, coordScaledAdd,
    coordScaledMul, coordScaledPow, coordScaledScaleBy,
    ScaledIntegerPower.pow, ScaledIntegerPower.mul,
    ScaledIntegerPower.scaleBy, ScaledIntegerPower.sub,
    ScaledIntegerPower.neg, ScaledIntegerPower.add,
    ScaledIntegerPower.constant, ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.zero,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_log_four_numerator_expansion :
    coordScaledLogFourNumerator =
      coordScaledLogFourNumeratorData := by
  rw [coordScaledLogFourNumerator, coord_scaled_t_expansion]
  exact coord_scaled_log_four_numerator_from_t

set_option maxRecDepth 100000 in
lemma coord_scaled_coord_log_upper_from_t :
    coordScaledCoordLogUpper
        (coordScaledAdd (coordScaledInts [1]) coordScaledTData) =
      coordScaledCoordLogUpperData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledCoordLogUpperData,
    coordScaledCoordLogUpperDataScale,
    coordScaledCoordLogUpperDataCoefficients,
    coordScaledCoordLogUpper, coordScaledTData,
    coordScaledTDataScale, coordScaledTDataCoefficients,
    coordScaledInts, coordScaledRats, coordScaledConstant,
    coordScaledSub, coordScaledNeg, coordScaledAdd,
    coordScaledComp, coordScaledScaleBy,
    ScaledIntegerPower.comp, ScaledIntegerPower.compAux,
    ScaledIntegerPower.mul, ScaledIntegerPower.scaleBy,
    ScaledIntegerPower.sub, ScaledIntegerPower.neg,
    ScaledIntegerPower.add, ScaledIntegerPower.constant,
    ScaledIntegerPower.ofIntegers, ScaledIntegerPower.zero,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_coord_log_upper_expansion :
    coordScaledCoordLogUpper
        (coordScaledAdd (coordScaledInts [1]) coordScaledT) =
      coordScaledCoordLogUpperData := by
  rw [coord_scaled_t_expansion]
  exact coord_scaled_coord_log_upper_from_t

set_option maxRecDepth 100000 in
lemma coord_scaled_old_correction_from_t :
    coordScaledComp
        (coordScaledRats 200 [-50, 68, 39, -16])
        coordScaledTData =
      coordScaledOldCorrectionAtTData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledOldCorrectionAtTData,
    coordScaledOldCorrectionAtTDataScale,
    coordScaledOldCorrectionAtTDataCoefficients,
    coordScaledTData, coordScaledTDataScale,
    coordScaledTDataCoefficients,
    coordScaledRats, coordScaledComp,
    ScaledIntegerPower.comp, ScaledIntegerPower.compAux,
    ScaledIntegerPower.mul, ScaledIntegerPower.add,
    ScaledIntegerPower.constant, ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.zero,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_old_correction_expansion :
    coordScaledOldCorrectionAtT =
      coordScaledOldCorrectionAtTData := by
  rw [coordScaledOldCorrectionAtT, coord_scaled_t_expansion]
  exact coord_scaled_old_correction_from_t

set_option maxRecDepth 100000 in
lemma coord_scaled_taylor_five_from_t :
    coordScaledComp
        (coordScaledRats 120 [120, -120, 60, -20, 5, -1])
        coordScaledTData =
      coordScaledTaylorFiveAtTData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledTaylorFiveAtTData,
    coordScaledTaylorFiveAtTDataScale,
    coordScaledTaylorFiveAtTDataCoefficients,
    coordScaledTData, coordScaledTDataScale,
    coordScaledTDataCoefficients,
    coordScaledRats, coordScaledComp,
    ScaledIntegerPower.comp, ScaledIntegerPower.compAux,
    ScaledIntegerPower.mul, ScaledIntegerPower.add,
    ScaledIntegerPower.constant, ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.zero,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_taylor_five_expansion :
    coordScaledTaylorFiveAtT = coordScaledTaylorFiveAtTData := by
  rw [coordScaledTaylorFiveAtT, coord_scaled_t_expansion]
  exact coord_scaled_taylor_five_from_t

set_option maxRecDepth 100000 in
lemma coord_scaled_error_six_from_t :
    coordScaledComp
        (coordScaledRats 4320 [0, 0, 0, 0, 0, 0, 7])
        coordScaledTData =
      coordScaledErrorSixAtTData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledErrorSixAtTData,
    coordScaledErrorSixAtTDataScale,
    coordScaledErrorSixAtTDataCoefficients,
    coordScaledTData, coordScaledTDataScale,
    coordScaledTDataCoefficients,
    coordScaledRats, coordScaledComp,
    ScaledIntegerPower.comp, ScaledIntegerPower.compAux,
    ScaledIntegerPower.mul, ScaledIntegerPower.add,
    ScaledIntegerPower.constant, ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.zero,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_error_six_expansion :
    coordScaledErrorSixAtT = coordScaledErrorSixAtTData := by
  rw [coordScaledErrorSixAtT, coord_scaled_t_expansion]
  exact coord_scaled_error_six_from_t

set_option maxRecDepth 100000 in
lemma coord_scaled_b_other_from_data :
    coordScaledAdd coordScaledCoordLogUpperData
        (coordScaledAdd
          (coordScaledMul coordScaledOldCorrectionAtTData
            coordScaledTaylorFiveAtTData)
          (coordScaledScaleBy 1 4 coordScaledErrorSixAtTData)) =
      coordScaledBOtherData := by
  norm_num (config := { maxSteps := 10000000 })
    [coordScaledBOtherData,
    coordScaledBOtherDataScale, coordScaledBOtherDataCoefficients,
    coordScaledCoordLogUpperData,
    coordScaledCoordLogUpperDataScale,
    coordScaledCoordLogUpperDataCoefficients,
    coordScaledOldCorrectionAtTData,
    coordScaledOldCorrectionAtTDataScale,
    coordScaledOldCorrectionAtTDataCoefficients,
    coordScaledTaylorFiveAtTData,
    coordScaledTaylorFiveAtTDataScale,
    coordScaledTaylorFiveAtTDataCoefficients,
    coordScaledErrorSixAtTData,
    coordScaledErrorSixAtTDataScale,
    coordScaledErrorSixAtTDataCoefficients,
    coordScaledRats, coordScaledAdd, coordScaledMul,
    coordScaledScaleBy,
    ScaledIntegerPower.mul, ScaledIntegerPower.scaleBy,
    ScaledIntegerPower.add, ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerMul, integerPowerShift,
    integerPowerScale, integerPowerAdd, decimalNat]

lemma coord_scaled_b_other_expansion :
    coordScaledBOther = coordScaledBOtherData := by
  rw [coordScaledBOther,
    coord_scaled_coord_log_upper_expansion,
    coord_scaled_old_correction_expansion,
    coord_scaled_taylor_five_expansion,
    coord_scaled_error_six_expansion]
  exact coord_scaled_b_other_from_data

end

end BackwardCoordRound2Back1Certificate
end Arxiv2407_19026
