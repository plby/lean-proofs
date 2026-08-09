import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateOneAffine

/-! Bernstein tail 120 for the first limit-certificate range. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_one_tail_120 :
    beta0BernsteinPower 8
        beta0LimitCoeffsOneTail120 =
      beta0LimitBernsteinOneTail120 := by
  norm_num (config := { maxSteps := 10000000 })
    [beta0LimitCoeffsOneTail120,
    beta0LimitBernsteinOneTail120,
    beta0BernsteinPower, rationalPowerPow,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
