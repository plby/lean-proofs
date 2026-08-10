import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeAffine20

/-! Affine tail 10 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxHeartbeats 500000 in
-- This exact ten-coefficient affine update exceeds the default heartbeat budget.
lemma beta0_limit_affine_three_tail_10 :
    rationalPowerComp beta0LimitSourceOneTail10
        [1 / 10, 2 / 5] =
      beta0LimitAffineThreeTail10 := by
  rw [beta0LimitSourceOneTail10,
    rational_power_comp_append,
    beta0_limit_affine_three_tail_20]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineThreeTail20,
    beta0LimitAffineThreeTail10,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
