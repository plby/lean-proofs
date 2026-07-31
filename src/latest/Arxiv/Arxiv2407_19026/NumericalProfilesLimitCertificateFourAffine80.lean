import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourAffine90

/-! Affine tail 80 for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_four_tail_80 :
    rationalPowerComp beta0LimitSourceOneTail80
        [1 / 2, 1 / 2] =
      beta0LimitAffineFourTail80 := by
  rw [beta0LimitSourceOneTail80,
    rational_power_comp_append,
    beta0_limit_affine_four_tail_90]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineFourTail90,
    beta0LimitAffineFourTail80,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
