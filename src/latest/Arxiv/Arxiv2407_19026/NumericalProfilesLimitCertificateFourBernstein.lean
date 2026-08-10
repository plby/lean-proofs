import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourBernstein0

/-! Complete Bernstein expansion for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_four_expansion :
    rationalPowerScale (1 / beta0LimitScaleFour)
        (beta0BernsteinPower 128 beta0LimitCoeffsFour) =
      beta0LimitLocalFourExpanded := by
  rw [beta0LimitCoeffsFour,
    beta0_limit_bernstein_four_tail_0]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerScale, beta0LimitScaleFour,
    beta0LimitBernsteinFourTail0,
    beta0LimitLocalFourExpanded,
    beta0LimitAffineFourTail0,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
