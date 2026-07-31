import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2BookCells0

/-! Exact Horner cells 4–7 for the Round 3 Back2 book margin. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

set_option maxHeartbeats 500000 in
-- Exact Horner evaluation on this cell exceeds the default heartbeat budget.
set_option maxRecDepth 100000 in
-- The recursive degree-170 rational interval calculation exceeds Lean's default recursion depth.
lemma book_cell_4_horner :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 4 / 16, hi := 5 / 16,
            le := by norm_num } :
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

set_option maxHeartbeats 500000 in
-- Exact Horner evaluation on this cell exceeds the default heartbeat budget.
set_option maxRecDepth 100000 in
-- The recursive degree-170 rational interval calculation exceeds Lean's default recursion depth.
lemma book_cell_5_horner :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 5 / 16, hi := 6 / 16,
            le := by norm_num } :
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

set_option maxHeartbeats 500000 in
-- Exact Horner evaluation on this cell exceeds the default heartbeat budget.
set_option maxRecDepth 100000 in
-- The recursive degree-170 rational interval calculation exceeds Lean's default recursion depth.
lemma book_cell_6_horner :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 6 / 16, hi := 7 / 16,
            le := by norm_num } :
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

set_option maxHeartbeats 500000 in
-- Exact Horner evaluation on this cell exceeds the default heartbeat budget.
set_option maxRecDepth 100000 in
-- The recursive degree-170 rational interval calculation exceeds Lean's default recursion depth.
lemma book_cell_7_horner :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 7 / 16, hi := 8 / 16,
            le := by norm_num } :
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

end BackwardBookRound3Back2Certificate
end Arxiv2407_19026
