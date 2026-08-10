import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourAffine40

/-! Affine tail 30 for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_four_tail_30 :
    rationalPowerComp beta0LimitSourceOneTail30
        [1 / 2, 1 / 2] =
      beta0LimitAffineFourTail30 := by
  rw [beta0LimitSourceOneTail30,
    rational_power_comp_append,
    beta0_limit_affine_four_tail_40]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineFourTail40,
    beta0LimitAffineFourTail30,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
