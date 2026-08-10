import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateAffine120

/-! Affine-certificate tail starting at coefficient 110. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

lemma book_affine_tail110 :
    integerPowerAffine 5 3 2 bookNumeratorTail110 =
      bookAffineTail110 := by
  rw [bookNumeratorTail110]
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
  rw [book_affine_tail120]
  norm_num (config := { maxSteps := 10000000 })
    [List.length_append,
    bookNumeratorTail120_length,
    bookAffineTail110, bookAffineTail120,
    integerPowerAdd, integerPowerLinear,
    integerPowerLinearTail, decimalNat]

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
