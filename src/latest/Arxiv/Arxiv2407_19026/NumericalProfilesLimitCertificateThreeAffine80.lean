import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeAffine90

/-! Affine tail 80 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_three_tail_80 :
    rationalPowerComp beta0LimitSourceOneTail80
        [1 / 10, 2 / 5] =
      beta0LimitAffineThreeTail80 := by
  rw [beta0LimitSourceOneTail80,
    rational_power_comp_append,
    beta0_limit_affine_three_tail_90]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineThreeTail90,
    beta0LimitAffineThreeTail80,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
