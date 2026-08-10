import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateAffine5

/-! Affine-certificate tail starting at coefficient 0. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

set_option maxHeartbeats 500000 in
-- Exact arithmetic for this 171-coefficient affine tail exceeds the default heartbeat budget.
set_option maxRecDepth 100000 in
-- The final affine-tail arithmetic exceeds the default simplifier recursion depth.
lemma book_affine_tail0 :
    integerPowerAffine 5 3 2 bookNumeratorTail0 =
      bookAffineTail0 := by
  rw [bookNumeratorTail0]
  simp only [List.cons_append, List.nil_append]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [book_affine_tail5]
  norm_num (config := { maxSteps := 10000000 })
    [List.length_append,
    bookNumeratorTail5_length,
    bookAffineTail0, bookAffineTail5,
    integerPowerAdd, integerPowerLinear,
    integerPowerLinearTail, decimalNat]

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
