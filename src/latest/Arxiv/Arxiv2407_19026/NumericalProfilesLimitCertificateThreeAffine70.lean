import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeAffine80

/-! Affine tail 70 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_three_tail_70 :
    rationalPowerComp beta0LimitSourceOneTail70
        [1 / 10, 2 / 5] =
      beta0LimitAffineThreeTail70 := by
  rw [beta0LimitSourceOneTail70,
    rational_power_comp_append,
    beta0_limit_affine_three_tail_80]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineThreeTail80,
    beta0LimitAffineThreeTail70,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
