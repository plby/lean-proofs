import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2CertificateAffine25

/-! Affine-certificate tail starting at coefficient 20. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

set_option maxHeartbeats 500000 in
-- Exact arithmetic for this 151-coefficient affine tail exceeds the default heartbeat budget.
set_option maxRecDepth 100000 in
-- The final affine-tail arithmetic exceeds the default simplifier recursion depth.
lemma book_affine_tail20 :
    integerPowerAffine 5 3 2 bookNumeratorTail20 =
      bookAffineTail20 := by
  rw [bookNumeratorTail20]
  simp only [List.cons_append, List.nil_append]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [integer_power_affine_cons]
  rw [book_affine_tail25]
  norm_num (config := { maxSteps := 10000000 })
    [List.length_append,
    bookNumeratorTail25_length,
    bookAffineTail20, bookAffineTail25,
    integerPowerAdd, integerPowerLinear,
    integerPowerLinearTail, decimalNat]

end

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
