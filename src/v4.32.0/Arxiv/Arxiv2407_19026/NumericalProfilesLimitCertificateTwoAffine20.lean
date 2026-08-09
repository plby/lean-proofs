import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoAffine30

/-! Affine tail 20 for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_two_tail_20 :
    rationalPowerComp beta0LimitSourceOneTail20
        [1 / 100, 9 / 100] =
      beta0LimitAffineTwoTail20 := by
  rw [beta0LimitSourceOneTail20,
    rational_power_comp_append,
    beta0_limit_affine_two_tail_30]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineTwoTail30,
    beta0LimitAffineTwoTail20,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
