import Arxiv.Arxiv2407_19026.TangentBackwardBookRound1Back2Certificate

/-!
# Exact blue-fit identity for the first-round second backward interval

This file isolates the large rational identity relating the certified
degree-49 numerator to the semantic blue upper bound.
-/

namespace Arxiv2407_19026
namespace BackwardBookRound1Back2Bounds

noncomputable section

open BackwardBookRound1Back2Certificate

def backwardBlueUpperRound1Back2 (z : ℝ) : ℝ :=
  (46095949483 / 1000000000000) +
    (93935093229 / 100000000000) * z +
    (-116155023031 / 125000000000) * z ^ 2 +
    (527782166713 / 1000000000000) * z ^ 3 +
    (-60151849199 / 500000000000) * z ^ 4

set_option maxHeartbeats 0 in
-- Normalizing the exact degree-49 rational blue-fit identity exceeds the default budget.
set_option maxRecDepth 30000 in
-- Expanding the certified coefficient lists needs additional simplifier recursion.
lemma blue_fit_sub_raw_identity {z : ℝ} (hzplus : 0 < 1 + z) :
    backwardBlueUpperRound1Back2 z -
        backwardBlueRawUpper (9 / 200) z =
      (evalPower bluePowerCoeffs z / bluePowerScale) /
        (1 + z) := by
  dsimp [backwardBlueRawUpper, backwardExpQUpper,
    backwardQUpper, mediumCorrectionPolynomial,
    backwardBlueUpperRound1Back2]
  norm_num [KernelBounds.expNegTaylor9,
    KernelBounds.expNegError10, Finset.sum_range_succ,
    Nat.factorial]
  dsimp [evalPower, bluePowerCoeffs, bluePowerScale,
    decimalNat]
  field_simp [hzplus.ne']
  ring

end

end BackwardBookRound1Back2Bounds
end Arxiv2407_19026
