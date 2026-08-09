import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateOneBernstein90

/-! Bernstein tail 80 for the first limit-certificate range. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxHeartbeats 500000 in
-- This exact ten-coefficient Bernstein update exceeds the default heartbeat budget.
lemma beta0_limit_bernstein_one_tail_80 :
    beta0BernsteinPower 48
        beta0LimitCoeffsOneTail80 =
      beta0LimitBernsteinOneTail80 := by
  rw [beta0LimitCoeffsOneTail80,
    beta0_bernstein_power_append 48 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_one_tail_90]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinOneTail90,
    beta0LimitBernsteinOneTail80,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
