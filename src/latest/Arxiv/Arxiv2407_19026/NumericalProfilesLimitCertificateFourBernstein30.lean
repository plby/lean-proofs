import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateFourBernstein40

/-! Bernstein tail 30 for limit-certificate range four. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxRecDepth 10000 in
-- This exact Bernstein tail exceeds Lean's default recursion depth.
lemma beta0_limit_bernstein_four_tail_30 :
    beta0BernsteinPower 98
        beta0LimitCoeffsFourTail30 =
      beta0LimitBernsteinFourTail30 := by
  rw [beta0LimitCoeffsFourTail30,
    beta0_bernstein_power_append 98 _ _
      (by norm_num)]
  norm_num only [List.length_cons, List.length_nil,
    Nat.reduceSub]
  rw [beta0_limit_bernstein_four_tail_40]
  norm_num (config := { maxSteps := 10000000 })
    [beta0BernsteinPowerWithTail,
    beta0LimitBernsteinFourTail40,
    beta0LimitBernsteinFourTail30,
    rationalPowerPow, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

end

end Arxiv2407_19026
