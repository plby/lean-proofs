import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateAffine50

/-! Affine-certificate tail starting at coefficient 40. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

set_option maxHeartbeats 500000 in
-- Exact arithmetic for this 131-coefficient affine tail exceeds the default heartbeat budget.
lemma book_affine_tail40 :
    integerPowerAffine 5 3 2 bookNumeratorTail40 =
      bookAffineTail40 := by
  rw [bookNumeratorTail40]
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
  rw [book_affine_tail50]
  norm_num (config := { maxSteps := 10000000 })
    [List.length_append,
    bookNumeratorTail50_length,
    bookAffineTail40, bookAffineTail50,
    integerPowerAdd, integerPowerLinear,
    integerPowerLinearTail, decimalNat]

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
