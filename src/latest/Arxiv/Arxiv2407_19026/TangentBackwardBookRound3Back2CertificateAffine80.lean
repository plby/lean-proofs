import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateAffine90

/-! Affine-certificate tail starting at coefficient 80. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

set_option maxHeartbeats 500000 in
-- Exact arithmetic for this 91-coefficient affine tail exceeds the default heartbeat budget.
lemma book_affine_tail80 :
    integerPowerAffine 5 3 2 bookNumeratorTail80 =
      bookAffineTail80 := by
  rw [bookNumeratorTail80]
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
  rw [book_affine_tail90]
  norm_num (config := { maxSteps := 10000000 })
    [List.length_append,
    bookNumeratorTail90_length,
    bookAffineTail80, bookAffineTail90,
    integerPowerAdd, integerPowerLinear,
    integerPowerLinearTail, decimalNat]

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
