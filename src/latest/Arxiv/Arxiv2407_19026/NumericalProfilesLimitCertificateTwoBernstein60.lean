import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoBernstein70

/-! Bernstein tail 60 for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxRecDepth 10000 in
-- This exact Bernstein tail exceeds Lean's default recursion depth.
lemma beta0_limit_bernstein_two_tail_60 :
    beta0BernsteinPower 68
        beta0LimitCoeffsTwoTail60 =
      beta0LimitBernsteinTwoTail60 := by
  rw [beta0LimitCoeffsTwoTail60,
    beta0_bernstein_power_append 68 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_two_tail_70]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinTwoTail70,
    beta0LimitBernsteinTwoTail60,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
