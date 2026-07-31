import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateOneBernstein110

/-! Bernstein tail 100 for the first limit-certificate range. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_one_tail_100 :
    beta0BernsteinPower 28
        beta0LimitCoeffsOneTail100 =
      beta0LimitBernsteinOneTail100 := by
  rw [beta0LimitCoeffsOneTail100,
    beta0_bernstein_power_append 28 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_one_tail_110]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinOneTail110,
    beta0LimitBernsteinOneTail100,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
