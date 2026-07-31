import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeAffine

/-! Bernstein tail 120 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_three_tail_120 :
    beta0BernsteinPower 8
        beta0LimitCoeffsThreeTail120 =
      beta0LimitBernsteinThreeTail120 := by
  norm_num (config := { maxSteps := 10000000 })
    [beta0LimitCoeffsThreeTail120,
    beta0LimitBernsteinThreeTail120,
    beta0BernsteinPower, rationalPowerPow,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
