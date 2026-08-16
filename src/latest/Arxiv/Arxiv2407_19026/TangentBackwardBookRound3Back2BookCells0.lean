import Arxiv.Arxiv2407_19026.TangentBackwardBookRound3Back2BookPowerData

/-! Exact Horner cells 0–15 for the Round 3 Back2 book margin. -/

namespace Arxiv2407_19026
namespace BackwardBookRound3Back2Certificate

noncomputable section

set_option maxRecDepth 100000 in
-- The recursive degree-170 rational interval calculation exceeds Lean's default recursion depth.
lemma book_cell_0_horner :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 0 / 16, hi := 1 / 16,
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
lemma book_cell_1_horner :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 1 / 16, hi := 2 / 16,
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
lemma book_cell_2_horner :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 2 / 16, hi := 3 / 16,
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
lemma book_cell_3_horner :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 3 / 16, hi := 4 / 16,
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

set_option maxHeartbeats 500000 in
-- Exact Horner evaluation on this cell exceeds the default heartbeat budget.
set_option maxRecDepth 100000 in
-- The recursive degree-170 rational interval calculation exceeds Lean's default recursion depth.
lemma book_cell_8_horner :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 8 / 16, hi := 9 / 16,
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
lemma book_cell_9_horner :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 9 / 16, hi := 10 / 16,
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
lemma book_cell_10_horner :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 10 / 16, hi := 11 / 16,
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
lemma book_cell_11_horner :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 11 / 16, hi := 12 / 16,
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
lemma book_cell_12_horner :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 12 / 16, hi := 13 / 16,
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
lemma book_cell_13_horner :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 13 / 16, hi := 14 / 16,
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
lemma book_cell_14_horner :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 14 / 16, hi := 15 / 16,
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
lemma book_cell_15_horner :
    0 <
      (integerHornerInterval bookPowerCoeffs
        ({ lo := 15 / 16, hi := 16 / 16,
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
