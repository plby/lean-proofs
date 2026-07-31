import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateTwoData

/-! Affine tail 120 for limit-certificate range two. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_two_tail_120 :
    rationalPowerComp beta0LimitSourceOneTail120
        [1 / 100, 9 / 100] =
      beta0LimitAffineTwoTail120 := by
  norm_num (config := { maxSteps := 10000000 })
    [beta0LimitSourceOneTail120,
    beta0LimitAffineTwoTail120,
    rationalPowerComp, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
