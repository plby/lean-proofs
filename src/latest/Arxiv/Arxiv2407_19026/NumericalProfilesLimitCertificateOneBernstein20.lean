import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateOneBernstein30

/-! Bernstein tail 20 for the first limit-certificate range. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxHeartbeats 500000 in
-- This exact ten-coefficient Bernstein update exceeds the default heartbeat budget.
set_option maxRecDepth 10000 in
-- This exact Bernstein tail exceeds Lean's default recursion depth.
lemma beta0_limit_bernstein_one_tail_20 :
    beta0BernsteinPower 108
        beta0LimitCoeffsOneTail20 =
      beta0LimitBernsteinOneTail20 := by
  rw [beta0LimitCoeffsOneTail20,
    beta0_bernstein_power_append 108 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_one_tail_30]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinOneTail30,
    beta0LimitBernsteinOneTail20,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
