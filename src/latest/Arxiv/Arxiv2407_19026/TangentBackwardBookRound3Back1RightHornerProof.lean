import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back1RightData

/-! Reflected-coordinate Horner check for round 3, first backward-book interval. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back1Certificate

noncomputable section

set_option maxHeartbeats 0 in
-- Exact Horner evaluation of the reflected degree-110 margin exceeds the default budget.
set_option maxRecDepth 100000 in
-- Evaluating the reflected coefficient list needs deeper recursion.
lemma book_horner_lower_right_reflected :
    0 <
      (integerHornerInterval bookReflectedCoeffs
        ({ lo := 0, hi := 1 / 2, le := by norm_num } :
          LeanCert.Core.IntervalRat)).lo := by
  norm_num (config := { maxSteps := 10000000 })
    [integerHornerInterval, bookReflectedCoeffs,
    bookReflectedCoeffsData,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4,
    decimalNat]

end

end BackwardBookRound3Back1Certificate
end Arxiv2407_19026
