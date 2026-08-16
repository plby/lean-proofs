import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back1StageMiddle

/-! Mixed-product branch for the round-1 first backward-book expansion. -/

namespace Arxiv2407_19026
namespace BackwardBookRound1Back1Certificate

noncomputable section

set_option maxHeartbeats 500000 in
-- Normalizing the exact degree-110 Horner product exceeds the default heartbeat budget.
set_option maxRecDepth 5000 in
-- The nested Horner expression also exceeds the default recursion depth.
lemma book_bracket_entropy_product_eval (z : ℝ) :
    rationalPowerEval bookBracketNumeratorExpandedPower z *
        rationalPowerEval backwardEntropyDenominatorPower z =
      rationalPowerEval
        bookBracketEntropyProductExpandedPower z := by
  norm_num [decimalNat, bookBracketNumeratorExpandedPower,
    backwardEntropyDenominatorPower,
    bookBracketEntropyProductExpandedPower,
    rationalPowerPow, rationalPowerMul,
    rationalPowerShift, rationalPowerScale,
    rationalPowerAdd, rationalPowerEval]
  ring_nf (config := { mode := .raw })

lemma book_numerator_sum_expansion :
    rationalPowerAdd bookEntropyProductExpandedPower
        (rationalPowerScale (1 / 2)
          bookBracketEntropyProductExpandedPower) =
      bookNumeratorExpandedPower := by
  norm_num [decimalNat, bookEntropyProductExpandedPower,
    bookBracketEntropyProductExpandedPower,
    bookNumeratorExpandedPower,
    rationalPowerScale, rationalPowerAdd]


end

end BackwardBookRound1Back1Certificate
end Arxiv2407_19026
