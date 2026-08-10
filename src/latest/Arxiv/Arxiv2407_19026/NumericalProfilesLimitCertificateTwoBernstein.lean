import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoBernstein0

/-! Complete Bernstein expansion for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_two_expansion :
    rationalPowerScale (1 / beta0LimitScaleTwo)
        (beta0BernsteinPower 128 beta0LimitCoeffsTwo) =
      beta0LimitLocalTwoExpanded := by
  rw [beta0LimitCoeffsTwo,
    beta0_limit_bernstein_two_tail_0]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerScale, beta0LimitScaleTwo,
    beta0LimitBernsteinTwoTail0,
    beta0LimitLocalTwoExpanded,
    beta0LimitAffineTwoTail0,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
