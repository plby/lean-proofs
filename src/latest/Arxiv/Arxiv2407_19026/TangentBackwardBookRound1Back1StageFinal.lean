import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back1StageFinalBracket
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back1StageFinalEntropy
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back1StageFinalMixed

/-! Final composition for the round-1 first backward-book expansion. -/

namespace Arxiv2407_19026
namespace BackwardBookRound1Back1Certificate

noncomputable section

lemma book_numerator_eval (z : ℝ) :
    rationalPowerEval
        (backwardBookNumeratorTwoPower
          (2 / 25) (9 / 200) bookTPower bookBluePower) z =
      rationalPowerEval bookNumeratorExpandedPower z := by
  simp only [backwardBookNumeratorTwoPower,
    rationalPowerEval_add, rationalPowerEval_mul,
    rationalPowerEval_scale]
  rw [book_entropy_ramsey_expansion,
    book_blue_den_expansion, book_mu_den_expansion]
  rw [← rationalPowerEval_mul
      bookBlueDenExpandedPower bookMuDenExpandedPower z,
    book_den_product_expansion,
    ← rationalPowerEval_mul
      bookEntropyRamseyExpandedPower
        bookDenProductExpandedPower z,
    book_entropy_product_expansion,
    book_bracket_numerator_eval,
    book_bracket_entropy_product_eval]
  rw [← rationalPowerEval_scale,
    ← rationalPowerEval_add,
    book_numerator_sum_expansion]

end

end BackwardBookRound1Back1Certificate
end Arxiv2407_19026
