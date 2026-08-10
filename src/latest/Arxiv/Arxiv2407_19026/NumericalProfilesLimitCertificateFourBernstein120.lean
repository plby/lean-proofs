import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourAffine

/-! Bernstein tail 120 for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_four_tail_120 :
    beta0BernsteinPower 8
        beta0LimitCoeffsFourTail120 =
      beta0LimitBernsteinFourTail120 := by
  norm_num (config := { maxSteps := 10000000 })
    [beta0LimitCoeffsFourTail120,
    beta0LimitBernsteinFourTail120,
    beta0BernsteinPower, rationalPowerPow,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
