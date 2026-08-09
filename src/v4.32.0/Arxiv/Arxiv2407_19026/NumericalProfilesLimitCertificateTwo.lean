import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoBernstein

/-! Exact Bernstein certificate for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_two_identity :
    rationalPowerComp beta0LimitReserveExpandedPower
        [1 / 100, 9 / 100] =
      rationalPowerScale (1 / beta0LimitScaleTwo)
        (beta0BernsteinPower 128 beta0LimitCoeffsTwo) := by
  rw [beta0_limit_affine_two_expansion,
    beta0_limit_bernstein_two_expansion]

end

end Arxiv2407_19026
