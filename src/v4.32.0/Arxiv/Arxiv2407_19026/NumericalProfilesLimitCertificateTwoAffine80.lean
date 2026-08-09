import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoAffine90

/-! Affine tail 80 for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_two_tail_80 :
    rationalPowerComp beta0LimitSourceOneTail80
        [1 / 100, 9 / 100] =
      beta0LimitAffineTwoTail80 := by
  rw [beta0LimitSourceOneTail80,
    rational_power_comp_append,
    beta0_limit_affine_two_tail_90]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineTwoTail90,
    beta0LimitAffineTwoTail80,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
