import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateOneBernstein50

/-! Bernstein tail 40 for the first limit-certificate range. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxHeartbeats 500000 in
-- This exact ten-coefficient Bernstein update exceeds the default heartbeat budget.
set_option maxRecDepth 10000 in
-- This exact Bernstein tail exceeds Lean's default recursion depth.
lemma beta0_limit_bernstein_one_tail_40 :
    beta0BernsteinPower 88
        beta0LimitCoeffsOneTail40 =
      beta0LimitBernsteinOneTail40 := by
  rw [beta0LimitCoeffsOneTail40,
    beta0_bernstein_power_append 88 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_one_tail_50]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinOneTail50,
    beta0LimitBernsteinOneTail40,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
