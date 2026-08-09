import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeAffine100

/-! Affine tail 90 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_three_tail_90 :
    rationalPowerComp beta0LimitSourceOneTail90
        [1 / 10, 2 / 5] =
      beta0LimitAffineThreeTail90 := by
  rw [beta0LimitSourceOneTail90,
    rational_power_comp_append,
    beta0_limit_affine_three_tail_100]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineThreeTail100,
    beta0LimitAffineThreeTail90,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
