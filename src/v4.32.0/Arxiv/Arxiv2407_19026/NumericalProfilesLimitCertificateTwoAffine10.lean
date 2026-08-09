import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoAffine20

/-! Affine tail 10 for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxHeartbeats 500000 in
-- This exact ten-coefficient affine update exceeds the default heartbeat budget.
lemma beta0_limit_affine_two_tail_10 :
    rationalPowerComp beta0LimitSourceOneTail10
        [1 / 100, 9 / 100] =
      beta0LimitAffineTwoTail10 := by
  rw [beta0LimitSourceOneTail10,
    rational_power_comp_append,
    beta0_limit_affine_two_tail_20]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineTwoTail20,
    beta0LimitAffineTwoTail10,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
