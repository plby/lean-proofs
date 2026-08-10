import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourAffine110

/-! Affine tail 100 for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_four_tail_100 :
    rationalPowerComp beta0LimitSourceOneTail100
        [1 / 2, 1 / 2] =
      beta0LimitAffineFourTail100 := by
  rw [beta0LimitSourceOneTail100,
    rational_power_comp_append,
    beta0_limit_affine_four_tail_110]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineFourTail110,
    beta0LimitAffineFourTail100,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
