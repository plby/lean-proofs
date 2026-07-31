import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateOneBernstein100

/-! Bernstein tail 90 for the first limit-certificate range. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_one_tail_90 :
    beta0BernsteinPower 38
        beta0LimitCoeffsOneTail90 =
      beta0LimitBernsteinOneTail90 := by
  rw [beta0LimitCoeffsOneTail90,
    beta0_bernstein_power_append 38 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_one_tail_100]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinOneTail100,
    beta0LimitBernsteinOneTail90,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
