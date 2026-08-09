import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeBernstein70

/-! Bernstein tail 60 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxRecDepth 10000 in
-- This exact Bernstein tail exceeds Lean's default recursion depth.
lemma beta0_limit_bernstein_three_tail_60 :
    beta0BernsteinPower 68
        beta0LimitCoeffsThreeTail60 =
      beta0LimitBernsteinThreeTail60 := by
  rw [beta0LimitCoeffsThreeTail60,
    beta0_bernstein_power_append 68 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_three_tail_70]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinThreeTail70,
    beta0LimitBernsteinThreeTail60,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
