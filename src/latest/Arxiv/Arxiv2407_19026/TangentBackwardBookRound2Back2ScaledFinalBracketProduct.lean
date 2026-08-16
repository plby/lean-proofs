import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back2ScaledFinalBracketProductData

/-! Exact data check for the bracket/denominator product. -/

namespace Arxiv2407_19026
namespace BackwardBookRound2Back2Certificate

noncomputable section

set_option maxRecDepth 100000 in
lemma scaled_bracket_den_product_from_data :
    scaledMul scaledBookBracketData scaledDenProductData =
      scaledBracketDenProductData := by
  rfl

end

end BackwardBookRound2Back2Certificate
end Arxiv2407_19026
