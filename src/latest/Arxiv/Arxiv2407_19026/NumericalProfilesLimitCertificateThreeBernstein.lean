import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeBernstein0

/-! Complete Bernstein expansion for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_three_expansion :
    rationalPowerScale (1 / beta0LimitScaleThree)
        (beta0BernsteinPower 128 beta0LimitCoeffsThree) =
      beta0LimitLocalThreeExpanded := by
  rw [beta0LimitCoeffsThree,
    beta0_limit_bernstein_three_tail_0]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerScale, beta0LimitScaleThree,
    beta0LimitBernsteinThreeTail0,
    beta0LimitLocalThreeExpanded,
    beta0LimitAffineThreeTail0,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
