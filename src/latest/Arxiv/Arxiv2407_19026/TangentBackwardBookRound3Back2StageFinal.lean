import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2StageProductTwo

/-! Final exact coefficient expansion for the third-round second backward book interval. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

set_option maxHeartbeats 500000 in
-- Normalizing the final fourth-order numerator sum exceeds the default heartbeat budget.
set_option maxRecDepth 5000 in
-- The final fourth-order numerator coefficient lists exceed the default simplifier recursion depth.
lemma book_numerator_sum_expansion :
    rationalPowerAdd bookEntropyProductExpandedPower
        (rationalPowerScale (1 / 2)
          bookBracketEntropyProductExpandedPower) =
      bookNumeratorExpandedPower := by
  norm_num [decimalNat, bookEntropyProductExpandedPower,
    bookBracketEntropyProductExpandedPower,
    bookNumeratorExpandedPower,
    rationalPowerScale, rationalPowerAdd]

lemma book_numerator_eval (z : ℝ) :
    rationalPowerEval
        (backwardBookNumeratorFourPower
          (33 / 1000) (3 / 100) bookTPower bookBluePower) z =
      rationalPowerEval bookNumeratorExpandedPower z := by
  simp only [backwardBookNumeratorFourPower,
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

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
