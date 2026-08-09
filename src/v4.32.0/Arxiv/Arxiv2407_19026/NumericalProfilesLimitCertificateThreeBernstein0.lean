import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeBernstein10

/-! Bernstein tail 0 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxHeartbeats 500000 in
-- This exact ten-coefficient Bernstein update exceeds the default heartbeat budget.
set_option maxRecDepth 10000 in
-- This exact Bernstein tail exceeds Lean's default recursion depth.
lemma beta0_limit_bernstein_three_tail_0 :
    beta0BernsteinPower 128
        beta0LimitCoeffsThreeTail0 =
      beta0LimitBernsteinThreeTail0 := by
  rw [beta0LimitCoeffsThreeTail0,
    beta0_bernstein_power_append 128 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_three_tail_10]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinThreeTail10,
    beta0LimitBernsteinThreeTail0,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
