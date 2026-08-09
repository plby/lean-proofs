import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoAffine40

/-! Affine tail 30 for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_two_tail_30 :
    rationalPowerComp beta0LimitSourceOneTail30
        [1 / 100, 9 / 100] =
      beta0LimitAffineTwoTail30 := by
  rw [beta0LimitSourceOneTail30,
    rational_power_comp_append,
    beta0_limit_affine_two_tail_40]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineTwoTail40,
    beta0LimitAffineTwoTail30,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
