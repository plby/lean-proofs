import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeBernstein90

/-! Bernstein tail 80 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_three_tail_80 :
    beta0BernsteinPower 48
        beta0LimitCoeffsThreeTail80 =
      beta0LimitBernsteinThreeTail80 := by
  rw [beta0LimitCoeffsThreeTail80,
    beta0_bernstein_power_append 48 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_three_tail_90]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinThreeTail90,
    beta0LimitBernsteinThreeTail80,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
