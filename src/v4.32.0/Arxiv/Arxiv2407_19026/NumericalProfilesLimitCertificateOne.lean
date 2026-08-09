import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateOneBernstein

/-!
# Exact first-range certificate for the first-profile limit inequality

The rational polynomial remaining after the analytic estimates has a
nonnegative Bernstein expansion on `[3 / 1000, 1 / 100]`.
-/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_bernstein_one_identity :
    rationalPowerComp beta0LimitReserveExpandedPower
        [3 / 1000, 7 / 1000] =
      rationalPowerScale (1 / beta0LimitScaleOne)
        (beta0BernsteinPower 128 beta0LimitCoeffsOne) := by
  rw [beta0_limit_affine_one_expansion,
    beta0_limit_bernstein_one_expansion]

end

end Arxiv2407_19026
