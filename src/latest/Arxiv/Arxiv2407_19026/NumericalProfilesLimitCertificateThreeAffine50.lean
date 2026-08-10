import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeAffine60

/-! Affine tail 50 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_three_tail_50 :
    rationalPowerComp beta0LimitSourceOneTail50
        [1 / 10, 2 / 5] =
      beta0LimitAffineThreeTail50 := by
  rw [beta0LimitSourceOneTail50,
    rational_power_comp_append,
    beta0_limit_affine_three_tail_60]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineThreeTail60,
    beta0LimitAffineThreeTail50,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
