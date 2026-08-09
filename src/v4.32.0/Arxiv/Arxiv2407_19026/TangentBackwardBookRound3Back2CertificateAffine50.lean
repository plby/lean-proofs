import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateAffine60

/-! Affine-certificate tail starting at coefficient 50. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

set_option maxHeartbeats 500000 in
-- Exact arithmetic for this 121-coefficient affine tail exceeds the default heartbeat budget.
lemma book_affine_tail50 :
    integerPowerAffine 5 3 2 bookNumeratorTail50 =
      bookAffineTail50 := by
  rw [bookNumeratorTail50]
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
  rw [book_affine_tail60]
  norm_num (config := { maxSteps := 10000000 })
    [List.length_append,
    bookNumeratorTail60_length,
    bookAffineTail50, bookAffineTail60,
    integerPowerAdd, integerPowerLinear,
    integerPowerLinearTail, decimalNat]

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
