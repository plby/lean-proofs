import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeAffine70

/-! Affine tail 60 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_three_tail_60 :
    rationalPowerComp beta0LimitSourceOneTail60
        [1 / 10, 2 / 5] =
      beta0LimitAffineThreeTail60 := by
  rw [beta0LimitSourceOneTail60,
    rational_power_comp_append,
    beta0_limit_affine_three_tail_70]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineThreeTail70,
    beta0LimitAffineThreeTail60,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
