import Arxiv.Arxiv2407_19026.TangentNumerics

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound3Native

open TangentAffine

def β2 : ℚ := 33 / 1000
def β3 : ℚ := 3 / 100
def plateauT : Expr := c (99 / 100)

def forwardFine : List ℚ := fineBreakpoints 1000 1680
def forwardMedium : List ℚ := mediumBreakpoints 100 168
def plateauMedium : List ℚ := mediumBreakpoints 268 107
def back1Fine : List ℚ := fineBreakpoints 3750 2250
def back1Medium : List ℚ := mediumBreakpoints 375 225
def back2Fine : List ℚ := fineBreakpoints 6000 4000
def back2Medium : List ℚ := mediumBreakpoints 600 400

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma small_book_checks :
    checkLowerAffineCover (smallBookSlope β2 β3) (1 / 1000)
        cfg 0 bpsBookSlope = true ∧
      checkLowerAffineCover (smallBook β2 β3) (1 / 10000)
        cfg (1 / 50) bpsBook = true := by
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma forward_book_check :
    checkLowerAffineCover (forwardBook β2 β3 r3ForwardT)
      (1 / 1000000) cfg (1 / 10) forwardMedium = true := by
  native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma plateau_checks :
    checkLowerAffineCover (plateauLogLow β2 β3 plateauT) 0
        cfg (67 / 250) plateauMedium = true ∧
      checkLowerAffineCover (plateauLogHigh β2 β3 plateauT) 0
        cfg (67 / 250) plateauMedium = true ∧
      checkLowerAffineCover (plateauBook β2 β3 plateauT)
        (1 / 1000000) cfg (67 / 250) plateauMedium = true := by
  constructor
  · native_decide
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma back1_checks :
    checkLowerAffineCover (backwardLogCoord β2 β3 r3Back1T) 0
        cfg (3 / 8) back1Fine = true ∧
      checkLowerAffineCover (backwardBook β2 β3 r3Back1T)
        (1 / 1000000) cfg (3 / 8) back1Medium = true := by
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma back2_coord_check :
    checkLowerAffineCover (backwardLogCoord β2 β3 r3Back2T) 0
        cfg (3 / 5) back2Fine = true := by
  native_decide

end TangentRound3Native
end Arxiv2407_19026
