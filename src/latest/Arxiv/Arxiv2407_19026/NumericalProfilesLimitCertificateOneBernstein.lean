import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateOneBernstein0

/-! Complete Bernstein expansion for the first limit-certificate range. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxRecDepth 10000 in
-- Scaling the complete degree-128 coefficient list exceeds Lean's default recursion depth.
lemma beta0_limit_bernstein_one_expansion :
    rationalPowerScale (1 / beta0LimitScaleOne)
        (beta0BernsteinPower 128 beta0LimitCoeffsOne) =
      beta0LimitLocalOneExpanded := by
  rw [beta0LimitCoeffsOne,
    beta0_limit_bernstein_one_tail_0]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerScale, beta0LimitScaleOne,
    beta0LimitBernsteinOneTail0,
    beta0LimitLocalOneExpanded,
    beta0LimitAffineOneTail0,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
