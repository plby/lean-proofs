import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourAffine120

/-! Affine tail 110 for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_four_tail_110 :
    rationalPowerComp beta0LimitSourceOneTail110
        [1 / 2, 1 / 2] =
      beta0LimitAffineFourTail110 := by
  rw [beta0LimitSourceOneTail110,
    rational_power_comp_append,
    beta0_limit_affine_four_tail_120]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineFourTail120,
    beta0LimitAffineFourTail110,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
