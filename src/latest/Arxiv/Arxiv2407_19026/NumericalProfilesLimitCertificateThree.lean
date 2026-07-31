import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeBernstein

/-! Exact Bernstein certificate for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_three_identity :
    rationalPowerComp beta0LimitReserveExpandedPower
        [1 / 10, 2 / 5] =
      rationalPowerScale (1 / beta0LimitScaleThree)
        (beta0BernsteinPower 128 beta0LimitCoeffsThree) := by
  rw [beta0_limit_affine_three_expansion,
    beta0_limit_bernstein_three_expansion]

end

end Arxiv2407_19026
