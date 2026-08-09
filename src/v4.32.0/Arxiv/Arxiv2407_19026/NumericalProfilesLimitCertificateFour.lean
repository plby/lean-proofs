import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourBernstein

/-! Exact Bernstein certificate for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_four_identity :
    rationalPowerComp beta0LimitReserveExpandedPower
        [1 / 2, 1 / 2] =
      rationalPowerScale (1 / beta0LimitScaleFour)
        (beta0BernsteinPower 128 beta0LimitCoeffsFour) := by
  rw [beta0_limit_affine_four_expansion,
    beta0_limit_bernstein_four_expansion]

end

end Arxiv2407_19026
