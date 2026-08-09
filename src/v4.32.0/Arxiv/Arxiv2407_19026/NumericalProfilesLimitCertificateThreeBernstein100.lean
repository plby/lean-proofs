import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeBernstein110

/-! Bernstein tail 100 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_three_tail_100 :
    beta0BernsteinPower 28
        beta0LimitCoeffsThreeTail100 =
      beta0LimitBernsteinThreeTail100 := by
  rw [beta0LimitCoeffsThreeTail100,
    beta0_bernstein_power_append 28 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_three_tail_110]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinThreeTail110,
    beta0LimitBernsteinThreeTail100,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
