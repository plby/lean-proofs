import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateAffine170

/-! Affine-certificate tail starting at coefficient 160. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

lemma book_affine_tail160 :
    integerPowerAffine 5 3 2 bookNumeratorTail160 =
      bookAffineTail160 := by
  rw [bookNumeratorTail160]
  simp only [List.cons_append, List.nil_append]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [book_affine_tail170]
  norm_num (config := { maxSteps := 10000000 })
    [List.length_append,
    bookNumeratorTail170_length,
    bookAffineTail160, bookAffineTail170,
    integerPowerAdd, integerPowerLinear,
    integerPowerLinearTail, decimalNat]

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
