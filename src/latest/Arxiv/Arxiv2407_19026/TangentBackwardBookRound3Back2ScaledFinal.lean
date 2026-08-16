import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2ScaledBasicBlue
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2ScaledBasicMu
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2ScaledMiddleBracket
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2ScaledMiddleProducts
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2ScaledFinalBracketNumerator
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2ScaledFinalBracketEntropy
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2ScaledFinalEntropy
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2ScaledFinalBook

/-! Assembly of the independently checked scaled-integer expansions. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

lemma scaled_book_bracket_expansion :
    scaledBookBracket = scaledBookBracketData := by
  rw [scaledBookBracket, scaled_alog_expansion]
  exact scaled_book_bracket_from_data

lemma scaled_xlog_expansion :
    scaledXLogNumerator = scaledXLogNumeratorData := by
  rw [scaledXLogNumerator,
    scaled_blue_log_numerator_expansion,
    scaled_mu_expansion,
    scaled_mu_den_rest_expansion,
    scaled_mu_log_numerator_expansion,
    scaled_blue_den_expansion]
  exact scaled_xlog_from_data

lemma scaled_den_product_expansion :
    scaledDenProduct = scaledDenProductData := by
  rw [scaledDenProduct, scaled_blue_den_expansion,
    scaled_mu_expansion, scaled_mu_den_expansion]
  exact scaled_den_product_from_data

lemma scaled_bracket_numerator_expansion :
    scaledBracketNumerator = scaledBracketNumeratorData := by
  rw [scaledBracketNumerator, scaled_xlog_expansion,
    scaled_book_bracket_expansion,
    scaled_den_product_expansion]
  exact scaled_bracket_numerator_from_data

lemma scaled_entropy_product_expansion :
    scaledMul scaledEntropyRamseyNumerator scaledDenProduct =
      scaledEntropyProductData := by
  rw [scaled_entropy_ramsey_expansion,
    scaled_den_product_expansion]
  exact scaled_entropy_product_from_data

lemma scaled_bracket_entropy_product_expansion :
    scaledMul scaledBracketNumerator scaledEntropyDenominator =
      scaledBracketEntropyProductData := by
  rw [scaled_bracket_numerator_expansion]
  exact scaled_bracket_entropy_product_from_data

lemma scaled_book_numerator_equivalent :
    ScaledIntegerPower.Equivalent
      scaledBookNumerator scaledBookNumeratorData := by
  rw [scaledBookNumerator,
    scaled_entropy_product_expansion,
    scaled_bracket_entropy_product_expansion]
  exact scaled_book_numerator_from_data

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
