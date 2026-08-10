import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourBernstein110

/-! Bernstein tail 100 for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_four_tail_100 :
    beta0BernsteinPower 28
        beta0LimitCoeffsFourTail100 =
      beta0LimitBernsteinFourTail100 := by
  rw [beta0LimitCoeffsFourTail100,
    beta0_bernstein_power_append 28 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_four_tail_110]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinFourTail110,
    beta0LimitBernsteinFourTail100,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
