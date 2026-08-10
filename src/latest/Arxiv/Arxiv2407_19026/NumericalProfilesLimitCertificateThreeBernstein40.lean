import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeBernstein50

/-! Bernstein tail 40 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxRecDepth 10000 in
-- This exact Bernstein tail exceeds Lean's default recursion depth.
lemma beta0_limit_bernstein_three_tail_40 :
    beta0BernsteinPower 88
        beta0LimitCoeffsThreeTail40 =
      beta0LimitBernsteinThreeTail40 := by
  rw [beta0LimitCoeffsThreeTail40,
    beta0_bernstein_power_append 88 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_three_tail_50]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinThreeTail50,
    beta0LimitBernsteinThreeTail40,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
