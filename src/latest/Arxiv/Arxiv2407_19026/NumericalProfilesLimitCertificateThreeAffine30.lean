import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateThreeAffine40

/-! Affine tail 30 for limit-certificate range three. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_three_tail_30 :
    rationalPowerComp beta0LimitSourceOneTail30
        [1 / 10, 2 / 5] =
      beta0LimitAffineThreeTail30 := by
  rw [beta0LimitSourceOneTail30,
    rational_power_comp_append,
    beta0_limit_affine_three_tail_40]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineThreeTail40,
    beta0LimitAffineThreeTail30,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
