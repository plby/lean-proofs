import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeBernstein30

/-! Bernstein tail 20 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxRecDepth 10000 in
-- This exact Bernstein tail exceeds Lean's default recursion depth.
lemma beta0_limit_bernstein_three_tail_20 :
    beta0BernsteinPower 108
        beta0LimitCoeffsThreeTail20 =
      beta0LimitBernsteinThreeTail20 := by
  rw [beta0LimitCoeffsThreeTail20,
    beta0_bernstein_power_append 108 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_three_tail_30]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinThreeTail30,
    beta0LimitBernsteinThreeTail20,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
