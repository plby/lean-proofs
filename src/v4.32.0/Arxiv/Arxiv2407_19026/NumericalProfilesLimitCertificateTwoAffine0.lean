import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoAffine10

/-! Affine tail 0 for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxHeartbeats 500000 in
-- This exact ten-coefficient affine update exceeds the default heartbeat budget.
lemma beta0_limit_affine_two_tail_0 :
    rationalPowerComp beta0LimitSourceOneTail0
        [1 / 100, 9 / 100] =
      beta0LimitAffineTwoTail0 := by
  rw [beta0LimitSourceOneTail0,
    rational_power_comp_append,
    beta0_limit_affine_two_tail_10]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineTwoTail10,
    beta0LimitAffineTwoTail0,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
