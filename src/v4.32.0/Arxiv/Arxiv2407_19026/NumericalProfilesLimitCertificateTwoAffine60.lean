import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoAffine70

/-! Affine tail 60 for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_two_tail_60 :
    rationalPowerComp beta0LimitSourceOneTail60
        [1 / 100, 9 / 100] =
      beta0LimitAffineTwoTail60 := by
  rw [beta0LimitSourceOneTail60,
    rational_power_comp_append,
    beta0_limit_affine_two_tail_70]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineTwoTail70,
    beta0LimitAffineTwoTail60,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
