import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2ScaledMiddleProductsData

/-! Definitional checks for the two logarithmic products. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

set_option maxRecDepth 1000000 in
lemma scaled_blue_mu_den_product_from_data :
    scaledMul scaledBlueLogNumeratorData scaledMuDenRestData =
      scaledBlueMuDenProductData := by
  rfl

set_option maxRecDepth 1000000 in
lemma scaled_mu_blue_den_product_from_data :
    scaledMul scaledMuLogNumeratorData scaledBlueDenData =
      scaledMuBlueDenProductData := by
  rfl

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
