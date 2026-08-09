import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateOneBernstein60

/-! Bernstein tail 50 for the first limit-certificate range. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxRecDepth 10000 in
-- This exact Bernstein tail exceeds Lean's default recursion depth.
lemma beta0_limit_bernstein_one_tail_50 :
    beta0BernsteinPower 78
        beta0LimitCoeffsOneTail50 =
      beta0LimitBernsteinOneTail50 := by
  rw [beta0LimitCoeffsOneTail50,
    beta0_bernstein_power_append 78 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_one_tail_60]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinOneTail60,
    beta0LimitBernsteinOneTail50,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
