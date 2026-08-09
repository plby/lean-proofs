import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back2Certificate

/-!
# Exact blue-fit identity for the second-round second backward interval

This file isolates the large rational identity relating the certified
degree-49 numerator to the semantic blue upper bound.
-/

namespace Arxiv2407_19026
namespace BackwardBookRound2Back2Bounds

noncomputable section

open BackwardBookRound2Back2Certificate

def backwardBlueUpperRound2Back2 (z : ℝ) : ℝ :=
  (22442795951 / 500000000000) +
    (94984755763 / 100000000000) * z +
    (-939512012139 / 1000000000000) * z ^ 2 +
    (106225246233 / 200000000000) * z ^ 3 +
    (-30152688843 / 250000000000) * z ^ 4

set_option maxHeartbeats 500000 in
-- Normalizing the exact degree-49 rational blue-fit identity exceeds the default budget.
set_option maxRecDepth 30000 in
-- Expanding the certified coefficient lists needs additional simplifier recursion.
lemma blue_fit_sub_raw_identity {z : ℝ} (hzplus : 0 < 1 + z) :
    backwardBlueUpperRound2Back2 z -
        backwardBlueRawUpper (33 / 1000) z =
      (evalPower bluePowerCoeffs z / bluePowerScale) /
        (1 + z) := by
  dsimp [backwardBlueRawUpper, backwardExpQUpper,
    backwardQUpper, mediumCorrectionPolynomial,
    backwardBlueUpperRound2Back2]
  norm_num [KernelBounds.expNegTaylor9,
    KernelBounds.expNegError10, Finset.sum_range_succ,
    Nat.factorial]
  dsimp [evalPower, bluePowerCoeffs, bluePowerScale,
    decimalNat]
  field_simp [hzplus.ne']
  ring

end

end BackwardBookRound2Back2Bounds
end Arxiv2407_19026
