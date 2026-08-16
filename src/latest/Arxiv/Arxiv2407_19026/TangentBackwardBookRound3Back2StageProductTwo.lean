import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2StageProductOne

/-! Second exact product expansions for the third-round second backward book interval. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

lemma book_entropy_ramsey_expansion :
    backwardEntropyRamseyNumeratorPower (3 / 100) =
      bookEntropyRamseyExpandedPower := by
  norm_num [decimalNat, backwardEntropyRamseyNumeratorPower,
    backwardEntropyNumeratorPower,
    backwardEntropyDenominatorPower,
    backwardRamseyPower, backwardTaylorNinePower,
    backwardErrorTenPower,
    bookEntropyRamseyExpandedPower,
    rationalPowerPow, rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

set_option maxHeartbeats 500000 in
-- Normalizing the fourth-order entropy/denominator product exceeds the default heartbeat budget.
set_option maxRecDepth 5000 in
-- The exact entropy-product coefficient lists exceed the default simplifier recursion depth.
lemma book_entropy_product_expansion :
    rationalPowerMul
        bookEntropyRamseyExpandedPower
        bookDenProductExpandedPower =
      bookEntropyProductExpandedPower := by
  norm_num [decimalNat, bookEntropyRamseyExpandedPower,
    bookDenProductExpandedPower,
    bookEntropyProductExpandedPower,
    rationalPowerMul, rationalPowerShift,
    rationalPowerScale, rationalPowerAdd]

set_option maxHeartbeats 1000000 in
-- Normalizing the exact bracket/entropy Horner product exceeds the default heartbeat budget.
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

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
