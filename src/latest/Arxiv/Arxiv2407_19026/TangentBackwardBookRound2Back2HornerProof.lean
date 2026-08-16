import Arxiv.Arxiv2407_19026.TangentBackwardBookRound2Back2AffineData

/-! Exact Horner positivity check for the round-2 second backward-book certificate. -/

namespace Arxiv2407_19026
namespace BackwardBookRound2Back2Certificate

noncomputable section

set_option maxHeartbeats 0 in
-- Exact Horner interval evaluation of the degree-140 margin exceeds the default budget.
set_option maxRecDepth 100000 in
-- The recursive rational interval calculation needs a deeper recursion limit.
lemma book_horner_lower :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 0, hi := 1, le := by norm_num } :
          LeanCert.Core.IntervalRat)).lo := by
  norm_num (config := { maxSteps := 10000000 })
    [integerHornerInterval, bookPowerCoeffs,
    bookAffineTail0,
    LeanCert.Core.IntervalRat.singleton,
    LeanCert.Core.IntervalRat.add,
    LeanCert.Core.IntervalRat.mul,
    LeanCert.Core.IntervalRat.min4,
    LeanCert.Core.IntervalRat.max4,
    decimalNat]

end

end BackwardBookRound2Back2Certificate
end Arxiv2407_19026
