import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourAffine70

/-! Affine tail 60 for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_four_tail_60 :
    rationalPowerComp beta0LimitSourceOneTail60
        [1 / 2, 1 / 2] =
      beta0LimitAffineFourTail60 := by
  rw [beta0LimitSourceOneTail60,
    rational_power_comp_append,
    beta0_limit_affine_four_tail_70]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineFourTail70,
    beta0LimitAffineFourTail60,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
