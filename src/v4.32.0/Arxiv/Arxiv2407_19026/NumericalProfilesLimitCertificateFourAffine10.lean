import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourAffine20

/-! Affine tail 10 for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_four_tail_10 :
    rationalPowerComp beta0LimitSourceOneTail10
        [1 / 2, 1 / 2] =
      beta0LimitAffineFourTail10 := by
  rw [beta0LimitSourceOneTail10,
    rational_power_comp_append,
    beta0_limit_affine_four_tail_20]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineFourTail20,
    beta0LimitAffineFourTail10,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
