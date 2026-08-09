import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourAffine0

/-! Complete affine expansion for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_four_expansion :
    rationalPowerComp beta0LimitReserveExpandedPower
        [1 / 2, 1 / 2] =
      beta0LimitLocalFourExpanded := by
  rw [beta0_limit_source_one_tail_zero,
    beta0_limit_affine_four_tail_0]
  rfl

end

end Arxiv2407_19026
