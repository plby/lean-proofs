import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateAffine160

/-! Affine-certificate tail starting at coefficient 150. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

lemma book_affine_tail150 :
    integerPowerAffine 5 3 2 bookNumeratorTail150 =
      bookAffineTail150 := by
  rw [bookNumeratorTail150]
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
  rw [book_affine_tail160]
  norm_num (config := { maxSteps := 10000000 })
    [List.length_append,
    bookNumeratorTail160_length,
    bookAffineTail150, bookAffineTail160,
    integerPowerAdd, integerPowerLinear,
    integerPowerLinearTail, decimalNat]

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
