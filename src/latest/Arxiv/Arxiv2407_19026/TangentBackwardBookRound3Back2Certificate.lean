import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateAffine
import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2ScaledSemantics

/-! Final exact certificate for `TangentBackwardBookRound3Back2`. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

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
