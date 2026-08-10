import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoAffine100

/-! Affine tail 90 for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_two_tail_90 :
    rationalPowerComp beta0LimitSourceOneTail90
        [1 / 100, 9 / 100] =
      beta0LimitAffineTwoTail90 := by
  rw [beta0LimitSourceOneTail90,
    rational_power_comp_append,
    beta0_limit_affine_two_tail_100]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineTwoTail100,
    beta0LimitAffineTwoTail90,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
