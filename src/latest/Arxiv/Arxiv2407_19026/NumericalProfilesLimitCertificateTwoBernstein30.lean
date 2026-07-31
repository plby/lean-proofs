import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoBernstein40

/-! Bernstein tail 30 for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxHeartbeats 500000 in
-- This exact ten-coefficient Bernstein update exceeds the default heartbeat budget.
set_option maxRecDepth 10000 in
-- This exact Bernstein tail exceeds Lean's default recursion depth.
lemma beta0_limit_bernstein_two_tail_30 :
    beta0BernsteinPower 98
        beta0LimitCoeffsTwoTail30 =
      beta0LimitBernsteinTwoTail30 := by
  rw [beta0LimitCoeffsTwoTail30,
    beta0_bernstein_power_append 98 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_two_tail_40]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinTwoTail40,
    beta0LimitBernsteinTwoTail30,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
