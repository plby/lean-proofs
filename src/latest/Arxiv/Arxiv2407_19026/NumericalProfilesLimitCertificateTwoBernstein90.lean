import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoBernstein100

/-! Bernstein tail 90 for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_two_tail_90 :
    beta0BernsteinPower 38
        beta0LimitCoeffsTwoTail90 =
      beta0LimitBernsteinTwoTail90 := by
  rw [beta0LimitCoeffsTwoTail90,
    beta0_bernstein_power_append 38 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_two_tail_100]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinTwoTail100,
    beta0LimitBernsteinTwoTail90,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
