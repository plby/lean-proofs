import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateAffine130

/-! Affine-certificate tail starting at coefficient 120. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

lemma book_affine_tail120 :
    integerPowerAffine 5 3 2 bookNumeratorTail120 =
      bookAffineTail120 := by
  rw [bookNumeratorTail120]
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
  rw [book_affine_tail130]
  norm_num (config := { maxSteps := 10000000 })
    [List.length_append,
    bookNumeratorTail130_length,
    bookAffineTail120, bookAffineTail130,
    integerPowerAdd, integerPowerLinear,
    integerPowerLinearTail, decimalNat]

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
