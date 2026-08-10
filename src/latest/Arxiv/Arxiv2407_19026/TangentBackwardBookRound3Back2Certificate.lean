import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateAffine

/-! Final exact certificate for `TangentBackwardBookRound3Back2`. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

set_option maxHeartbeats 500000 in
-- Checking the 171 exact rational-to-integer coefficient conversions exceeds the default budget.
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
    bookNumeratorTail120,
    bookNumeratorTail130,
    bookNumeratorTail140,
    bookNumeratorTail150,
    bookNumeratorTail160,
    bookNumeratorTail170,
    decimalNat]

set_option maxRecDepth 100000 in
-- Rewriting the 171-coefficient rational list exceeds the default recursion depth.
lemma book_numerator_integer_eval (z : ℝ) :
    rationalPowerEval bookNumeratorExpandedPower z =
      evalIntegerPower bookNumeratorCoeffs z /
        bookNumeratorScale := by
  rw [book_numerator_integer_identity]
  exact rationalPowerEval_fromIntegers
    bookNumeratorScale bookNumeratorCoeffs z
      (by norm_num [bookNumeratorScale, decimalNat])

set_option maxRecDepth 100000 in
-- Specializing the affine evaluator to 171 coefficients exceeds the default recursion depth.
lemma book_affine_eval (u : ℝ) :
    evalIntegerPower bookPowerCoeffs u * 5 =
      5 ^ 171 *
        evalIntegerPower bookNumeratorCoeffs
          (((3 : ℝ) + (2 : ℝ) * u) / 5) := by
  rw [← book_power_coeffs_affine]
  have haffine :=
    evalIntegerPower_affine
      5 3 2 bookNumeratorCoeffs u (by norm_num)
  rw [bookNumeratorCoeffs,
    bookNumeratorTail0_length] at haffine
  exact haffine



end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
