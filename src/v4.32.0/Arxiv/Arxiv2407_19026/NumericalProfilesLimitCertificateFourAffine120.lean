import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourData

/-! Affine tail 120 for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_four_tail_120 :
    rationalPowerComp beta0LimitSourceOneTail120
        [1 / 2, 1 / 2] =
      beta0LimitAffineFourTail120 := by
  norm_num (config := { maxSteps := 10000000 })
    [beta0LimitSourceOneTail120,
    beta0LimitAffineFourTail120,
    rationalPowerComp, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
