import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoAffine0

/-! Complete affine expansion for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_two_expansion :
    rationalPowerComp beta0LimitReserveExpandedPower
        [1 / 100, 9 / 100] =
      beta0LimitLocalTwoExpanded := by
  rw [beta0_limit_source_one_tail_zero,
    beta0_limit_affine_two_tail_0]
  rfl

end

end Arxiv2407_19026
