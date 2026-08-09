import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoAffine50

/-! Affine tail 40 for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_two_tail_40 :
    rationalPowerComp beta0LimitSourceOneTail40
        [1 / 100, 9 / 100] =
      beta0LimitAffineTwoTail40 := by
  rw [beta0LimitSourceOneTail40,
    rational_power_comp_append,
    beta0_limit_affine_two_tail_50]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineTwoTail50,
    beta0LimitAffineTwoTail40,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
