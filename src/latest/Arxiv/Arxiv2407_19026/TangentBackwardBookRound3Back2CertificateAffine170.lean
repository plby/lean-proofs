import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateData

/-! Affine-certificate tail starting at coefficient 170. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

lemma integer_power_affine_cons
    (denominator : ℕ) (left width coefficient : ℤ)
    (coefficients : List ℤ) :
    integerPowerAffine denominator left width
        (coefficient :: coefficients) =
      integerPowerAdd
        [coefficient * denominator ^ coefficients.length]
        (integerPowerLinear left width
          (integerPowerAffine denominator left width coefficients)) := by
  rfl

lemma book_affine_tail170 :
    integerPowerAffine 5 3 2 bookNumeratorTail170 =
      bookAffineTail170 := by
  rfl

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
