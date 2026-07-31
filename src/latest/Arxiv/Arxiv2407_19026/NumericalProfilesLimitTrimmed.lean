import Arxiv.Arxiv2407_19026.NumericalProfilesLimitExpanded

/-! Evaluation equivalence for the trimmed degree-128 limit polynomial. -/

namespace Arxiv2407_19026

noncomputable section

set_option maxRecDepth 10000 in
-- Removing ten trailing zero coefficients exceeds Lean's default recursion depth.
lemma beta0_limit_reserve_expansion (z : ℝ) :
    rationalPowerEval beta0LimitReservePower z =
      rationalPowerEval beta0LimitReserveExpandedPower z := by
  rw [beta0_limit_reserve_full_expansion]
  norm_num [rationalPowerEval,
    beta0LimitReserveExpandedFull,
    beta0LimitReserveExpandedPower,
    beta0LimitDecimalNat]

end

end Arxiv2407_19026
