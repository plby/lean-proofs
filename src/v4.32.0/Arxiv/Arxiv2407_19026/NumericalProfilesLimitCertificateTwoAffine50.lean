import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoAffine60

/-! Affine tail 50 for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_two_tail_50 :
    rationalPowerComp beta0LimitSourceOneTail50
        [1 / 100, 9 / 100] =
      beta0LimitAffineTwoTail50 := by
  rw [beta0LimitSourceOneTail50,
    rational_power_comp_append,
    beta0_limit_affine_two_tail_60]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineTwoTail60,
    beta0LimitAffineTwoTail50,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
