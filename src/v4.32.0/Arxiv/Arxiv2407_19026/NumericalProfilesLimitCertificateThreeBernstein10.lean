import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeBernstein20

/-! Bernstein tail 10 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxHeartbeats 500000 in
-- This exact ten-coefficient Bernstein update exceeds the default heartbeat budget.
set_option maxRecDepth 10000 in
-- This exact Bernstein tail exceeds Lean's default recursion depth.
lemma beta0_limit_bernstein_three_tail_10 :
    beta0BernsteinPower 118
        beta0LimitCoeffsThreeTail10 =
      beta0LimitBernsteinThreeTail10 := by
  rw [beta0LimitCoeffsThreeTail10,
    beta0_bernstein_power_append 118 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_three_tail_20]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinThreeTail20,
    beta0LimitBernsteinThreeTail10,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
