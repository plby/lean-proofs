import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeData

/-! Affine tail 120 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_three_tail_120 :
    rationalPowerComp beta0LimitSourceOneTail120
        [1 / 10, 2 / 5] =
      beta0LimitAffineThreeTail120 := by
  norm_num (config := { maxSteps := 10000000 })
    [beta0LimitSourceOneTail120,
    beta0LimitAffineThreeTail120,
    rationalPowerComp, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
