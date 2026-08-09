import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourAffine100

/-! Affine tail 90 for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_four_tail_90 :
    rationalPowerComp beta0LimitSourceOneTail90
        [1 / 2, 1 / 2] =
      beta0LimitAffineFourTail90 := by
  rw [beta0LimitSourceOneTail90,
    rational_power_comp_append,
    beta0_limit_affine_four_tail_100]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineFourTail100,
    beta0LimitAffineFourTail90,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
