import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateAffine0

/-! Completed staged affine certificate for `TangentBackwardBookRound3Back2`. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

lemma book_power_coeffs_affine :
    integerPowerAffine 5 3 2 bookNumeratorCoeffs =
      bookPowerCoeffs := by
  simpa [bookNumeratorCoeffs, bookPowerCoeffs] using
    book_affine_tail0

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
