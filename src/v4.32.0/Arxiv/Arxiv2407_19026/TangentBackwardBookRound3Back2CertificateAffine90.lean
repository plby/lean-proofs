import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateAffine100

/-! Affine-certificate tail starting at coefficient 90. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

lemma book_affine_tail90 :
    integerPowerAffine 5 3 2 bookNumeratorTail90 =
      bookAffineTail90 := by
  rw [bookNumeratorTail90]
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
  rw [book_affine_tail100]
  norm_num (config := { maxSteps := 10000000 })
    [List.length_append,
    bookNumeratorTail100_length,
    bookAffineTail90, bookAffineTail100,
    integerPowerAdd, integerPowerLinear,
    integerPowerLinearTail, decimalNat]

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
