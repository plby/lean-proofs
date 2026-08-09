import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2Certificate

/-!
# Exact blue-fit identity for the third-round second backward interval

This file isolates the large rational identity relating the certified
degree-49 numerator to the semantic blue upper bound.
-/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Bounds

noncomputable section

open BackwardBookRound3Back2Certificate

def backwardBlueUpperRound3Back2 (z : ℝ) : ℝ :=
  (44580289499 / 1000000000000) +
    (952487157437 / 1000000000000) * z +
    (-188419160673 / 200000000000) * z ^ 2 +
    (66495797323 / 125000000000) * z ^ 3 +
    (-24137425587 / 200000000000) * z ^ 4

set_option maxHeartbeats 500000 in
-- Normalizing the exact degree-49 rational blue-fit identity exceeds the default budget.
set_option maxRecDepth 30000 in
-- Expanding the certified coefficient lists needs additional simplifier recursion.
lemma blue_fit_sub_raw_identity {z : ℝ} (hzplus : 0 < 1 + z) :
    backwardBlueUpperRound3Back2 z -
        backwardBlueRawUpper (3 / 100) z =
      (evalPower bluePowerCoeffs z / bluePowerScale) /
        (1 + z) := by
  dsimp [backwardBlueRawUpper, backwardExpQUpper,
    backwardQUpper, mediumCorrectionPolynomial,
    backwardBlueUpperRound3Back2]
  norm_num [KernelBounds.expNegTaylor9,
    KernelBounds.expNegError10, Finset.sum_range_succ,
    Nat.factorial]
  dsimp [evalPower, bluePowerCoeffs, bluePowerScale,
    decimalNat]
  field_simp [hzplus.ne']
  ring

end

end BackwardBookRound3Back2Bounds
end Arxiv2407_19026
