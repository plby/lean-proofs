import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourBernstein80

/-! Bernstein tail 70 for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_four_tail_70 :
    beta0BernsteinPower 58
        beta0LimitCoeffsFourTail70 =
      beta0LimitBernsteinFourTail70 := by
  rw [beta0LimitCoeffsFourTail70,
    beta0_bernstein_power_append 58 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_four_tail_80]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinFourTail80,
    beta0LimitBernsteinFourTail70,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
