import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2ScaledMiddleProductProofs

/-! Exact scaled-integer data checks for the logarithmic products. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

set_option maxRecDepth 100000 in
lemma scaled_xlog_from_data :
    scaledAdd
        (scaledMul scaledBlueLogNumeratorData scaledMuDenRestData)
        (scaledMul scaledMuLogNumeratorData scaledBlueDenData) =
      scaledXLogNumeratorData := by
  rw [scaled_blue_mu_den_product_from_data,
    scaled_mu_blue_den_product_from_data]
  norm_num (config := { maxSteps := 10000000 })
    [scaledXLogNumeratorData,
    scaledXLogNumeratorDataScale,
    scaledXLogNumeratorDataCoefficients,
    scaledBlueMuDenProductData,
    scaledBlueMuDenProductDataScale,
    scaledBlueMuDenProductDataCoefficients,
    scaledMuBlueDenProductData,
    scaledMuBlueDenProductDataScale,
    scaledMuBlueDenProductDataCoefficients,
    scaledRats, scaledAdd,
    ScaledIntegerPower.add,
    ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerScale, integerPowerAdd, decimalNat]

set_option maxRecDepth 1000000 in
lemma scaled_den_product_from_data :
    scaledMul scaledBlueDenData scaledMuDenData =
      scaledDenProductData := by
  rfl

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
