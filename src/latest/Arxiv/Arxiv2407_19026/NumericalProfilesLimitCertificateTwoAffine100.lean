import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoAffine110

/-! Affine tail 100 for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_two_tail_100 :
    rationalPowerComp beta0LimitSourceOneTail100
        [1 / 100, 9 / 100] =
      beta0LimitAffineTwoTail100 := by
  rw [beta0LimitSourceOneTail100,
    rational_power_comp_append,
    beta0_limit_affine_two_tail_110]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineTwoTail110,
    beta0LimitAffineTwoTail100,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
