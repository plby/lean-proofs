import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back2ScaledData

/-! Exact data check for the final scaled book numerator. -/

namespace Arxiv2407_19026
namespace BackwardBookRound1Back2Certificate

noncomputable section

set_option maxHeartbeats 1000000 in
-- Exact final integer sum and normalization exceed the default budget.
set_option maxRecDepth 100000 in
lemma scaled_book_numerator_from_data :
    ScaledIntegerPower.Equivalent
      (scaledAdd scaledEntropyProductData
        (scaledScaleBy 1 2 scaledBracketEntropyProductData))
      scaledBookNumeratorData := by
  norm_num (config := { maxSteps := 10000000 })
    [ScaledIntegerPower.Equivalent,
    scaledBookNumeratorData,
    scaledEntropyProductData,
    scaledEntropyProductDataScale,
    scaledEntropyProductDataCoefficients,
    scaledBracketEntropyProductData,
    scaledBracketEntropyProductDataScale,
    scaledBracketEntropyProductDataCoefficients,
    scaledRats, scaledAdd, scaledScaleBy,
    ScaledIntegerPower.scaleBy,
    ScaledIntegerPower.add,
    ScaledIntegerPower.ofIntegers,
    ScaledIntegerPower.integerNatQuotient,
    integerPowerScale, integerPowerAdd,
    bookNumeratorScale, bookNumeratorCoeffs,
    bookNumeratorTail0, bookNumeratorTail5,
    bookNumeratorTail10, bookNumeratorTail15,
    bookNumeratorTail20, bookNumeratorTail25,
    bookNumeratorTail30, bookNumeratorTail35,
    bookNumeratorTail40, bookNumeratorTail50,
    bookNumeratorTail60, bookNumeratorTail70,
    bookNumeratorTail80, bookNumeratorTail90,
    bookNumeratorTail100, bookNumeratorTail110,
    decimalNat]

end

end BackwardBookRound1Back2Certificate
end Arxiv2407_19026
