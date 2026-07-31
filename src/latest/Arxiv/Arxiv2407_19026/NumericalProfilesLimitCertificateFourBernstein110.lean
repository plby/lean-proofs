import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourBernstein120

/-! Bernstein tail 110 for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_four_tail_110 :
    beta0BernsteinPower 18
        beta0LimitCoeffsFourTail110 =
      beta0LimitBernsteinFourTail110 := by
  rw [beta0LimitCoeffsFourTail110,
    beta0_bernstein_power_append 18 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_four_tail_120]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinFourTail120,
    beta0LimitBernsteinFourTail110,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
