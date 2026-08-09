import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoBernstein110

/-! Bernstein tail 100 for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_two_tail_100 :
    beta0BernsteinPower 28
        beta0LimitCoeffsTwoTail100 =
      beta0LimitBernsteinTwoTail100 := by
  rw [beta0LimitCoeffsTwoTail100,
    beta0_bernstein_power_append 28 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_two_tail_110]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinTwoTail110,
    beta0LimitBernsteinTwoTail100,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
