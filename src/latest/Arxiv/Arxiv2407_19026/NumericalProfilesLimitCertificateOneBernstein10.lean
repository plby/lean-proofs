import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateOneBernstein20

/-! Bernstein tail 10 for the first limit-certificate range. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxHeartbeats 500000 in
-- This exact ten-coefficient Bernstein update exceeds the default heartbeat budget.
set_option maxRecDepth 10000 in
-- This exact Bernstein tail exceeds Lean's default recursion depth.
lemma beta0_limit_bernstein_one_tail_10 :
    beta0BernsteinPower 118
        beta0LimitCoeffsOneTail10 =
      beta0LimitBernsteinOneTail10 := by
  rw [beta0LimitCoeffsOneTail10,
    beta0_bernstein_power_append 118 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_one_tail_20]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinOneTail20,
    beta0LimitBernsteinOneTail10,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
