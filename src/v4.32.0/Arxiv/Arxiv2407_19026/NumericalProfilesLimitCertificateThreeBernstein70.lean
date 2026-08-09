import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeBernstein80

/-! Bernstein tail 70 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_three_tail_70 :
    beta0BernsteinPower 58
        beta0LimitCoeffsThreeTail70 =
      beta0LimitBernsteinThreeTail70 := by
  rw [beta0LimitCoeffsThreeTail70,
    beta0_bernstein_power_append 58 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_three_tail_80]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinThreeTail80,
    beta0LimitBernsteinThreeTail70,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
