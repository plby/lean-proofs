import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeAffine50

/-! Affine tail 40 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_three_tail_40 :
    rationalPowerComp beta0LimitSourceOneTail40
        [1 / 10, 2 / 5] =
      beta0LimitAffineThreeTail40 := by
  rw [beta0LimitSourceOneTail40,
    rational_power_comp_append,
    beta0_limit_affine_three_tail_50]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineThreeTail50,
    beta0LimitAffineThreeTail40,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
