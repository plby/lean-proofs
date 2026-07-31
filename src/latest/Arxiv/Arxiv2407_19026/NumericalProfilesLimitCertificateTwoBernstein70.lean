import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoBernstein80

/-! Bernstein tail 70 for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxHeartbeats 500000 in
-- This exact ten-coefficient Bernstein update exceeds the default heartbeat budget.
lemma beta0_limit_bernstein_two_tail_70 :
    beta0BernsteinPower 58
        beta0LimitCoeffsTwoTail70 =
      beta0LimitBernsteinTwoTail70 := by
  rw [beta0LimitCoeffsTwoTail70,
    beta0_bernstein_power_append 58 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_two_tail_80]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinTwoTail80,
    beta0LimitBernsteinTwoTail70,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
