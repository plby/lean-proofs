import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourAffine60

/-! Affine tail 50 for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_four_tail_50 :
    rationalPowerComp beta0LimitSourceOneTail50
        [1 / 2, 1 / 2] =
      beta0LimitAffineFourTail50 := by
  rw [beta0LimitSourceOneTail50,
    rational_power_comp_append,
    beta0_limit_affine_four_tail_60]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineFourTail60,
    beta0LimitAffineFourTail50,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
