import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back1CertificateCore
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back1StageFinal

/-! Exact semantic bridge for the round-2 first backward-book certificate. -/

namespace Arxiv2407_19026
namespace BackwardBookRound2Back1Certificate

noncomputable section

set_option maxHeartbeats 500000 in
-- Checking the 111 exact rational-to-integer coefficient conversions exceeds the default budget.
set_option maxRecDepth 5000 in
-- The coefficient-list equality also exceeds the default recursion depth.
lemma book_numerator_integer_identity :
    bookNumeratorExpandedPower =
      rationalPowerFromIntegers
        bookNumeratorScale bookNumeratorCoeffs := by
  norm_num (config := { maxSteps := 10000000 })
    [bookNumeratorExpandedPower,
    rationalPowerFromIntegers,
    bookNumeratorScale, bookNumeratorCoeffs,
    bookNumeratorTail0,
    bookNumeratorTail5,
    bookNumeratorTail10,
    bookNumeratorTail15,
    bookNumeratorTail20,
    bookNumeratorTail25,
    bookNumeratorTail30,
    bookNumeratorTail35,
    bookNumeratorTail40,
    bookNumeratorTail50,
    bookNumeratorTail60,
    bookNumeratorTail70,
    bookNumeratorTail80,
    bookNumeratorTail90,
    bookNumeratorTail100,
    bookNumeratorTail110,
    decimalNat]

set_option maxRecDepth 100000 in
-- Rewriting the 111-coefficient rational list exceeds the default recursion depth.
lemma book_numerator_integer_eval (z : ℝ) :
    rationalPowerEval bookNumeratorExpandedPower z =
      evalIntegerPower bookNumeratorCoeffs z /
        bookNumeratorScale := by
  rw [book_numerator_integer_identity]
  exact rationalPowerEval_fromIntegers
    bookNumeratorScale bookNumeratorCoeffs z
      (by norm_num [bookNumeratorScale, decimalNat])


end

end BackwardBookRound2Back1Certificate
end Arxiv2407_19026
