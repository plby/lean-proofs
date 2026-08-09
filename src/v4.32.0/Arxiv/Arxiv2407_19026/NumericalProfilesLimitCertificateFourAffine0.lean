import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourAffine10

/-! Affine tail 0 for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_four_tail_0 :
    rationalPowerComp beta0LimitSourceOneTail0
        [1 / 2, 1 / 2] =
      beta0LimitAffineFourTail0 := by
  rw [beta0LimitSourceOneTail0,
    rational_power_comp_append,
    beta0_limit_affine_four_tail_10]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineFourTail10,
    beta0LimitAffineFourTail0,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
