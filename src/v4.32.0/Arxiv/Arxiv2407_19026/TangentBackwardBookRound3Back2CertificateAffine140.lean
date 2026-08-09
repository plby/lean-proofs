import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateAffine150

/-! Affine-certificate tail starting at coefficient 140. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

lemma book_affine_tail140 :
    integerPowerAffine 5 3 2 bookNumeratorTail140 =
      bookAffineTail140 := by
  rw [bookNumeratorTail140]
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
  rw [book_affine_tail150]
  norm_num (config := { maxSteps := 10000000 })
    [List.length_append,
    bookNumeratorTail150_length,
    bookAffineTail140, bookAffineTail150,
    integerPowerAdd, integerPowerLinear,
    integerPowerLinearTail, decimalNat]

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
