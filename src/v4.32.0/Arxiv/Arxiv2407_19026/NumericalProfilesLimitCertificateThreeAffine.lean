import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeAffine0

/-! Complete affine expansion for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_three_expansion :
    rationalPowerComp beta0LimitReserveExpandedPower
        [1 / 10, 2 / 5] =
      beta0LimitLocalThreeExpanded := by
  rw [beta0_limit_source_one_tail_zero,
    beta0_limit_affine_three_tail_0]
  rfl

end

end Arxiv2407_19026
