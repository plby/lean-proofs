import Arxiv.Arxiv2407_19026.TangentNumerics

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound2Native

open TangentAffine

def β1 : ℚ := 9 / 200
def β2 : ℚ := 33 / 1000
def plateauT : Expr := c (99 / 100)

def forwardFine : List ℚ := fineBreakpoints 1000 1680
def forwardMedium : List ℚ := mediumBreakpoints 100 168
def plateauMedium : List ℚ := mediumBreakpoints 268 110
def back1Fine : List ℚ := fineBreakpoints 3780 2220
def back1Medium : List ℚ := mediumBreakpoints 378 222
def back2Fine : List ℚ := fineBreakpoints 6000 4000
def back2Medium : List ℚ := mediumBreakpoints 600 400

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma small_checks :
    checkLowerAffineCover (smallCoordSlope β1 β2) (1 / 20)
        cfg 0 bpsSlope = true ∧
      checkLowerAffineCover (smallBookSlope β1 β2) (1 / 1000)
        cfg 0 bpsBookSlope = true ∧
      checkLowerAffineCover (smallBook β1 β2) (1 / 10000)
        cfg (1 / 50) bpsBook = true := by
  constructor
  · native_decide
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma forward_book_check :
    checkLowerAffineCover (forwardBook β1 β2 r2ForwardT)
      (1 / 1000000) cfg (1 / 10) forwardMedium = true := by
  native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma plateau_coord_checks :
    checkLowerAffineCover (plateauLogLow β1 β2 plateauT) 0
        cfg (67 / 250) plateauMedium = true ∧
      checkLowerAffineCover (plateauLogHigh β1 β2 plateauT) 0
        cfg (67 / 250) plateauMedium = true := by
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma back1_checks :
    checkLowerAffineCover (backwardLogCoord β1 β2 r2Back1T) 0
        cfg (189 / 500) back1Fine = true ∧
      checkLowerAffineCover (backwardBook β1 β2 r2Back1T)
        (1 / 1000000) cfg (189 / 500) back1Medium = true := by
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma back2_coord_check :
    checkLowerAffineCover (backwardLogCoord β1 β2 r2Back2T) 0
        cfg (3 / 5) back2Fine = true := by
  native_decide

end TangentRound2Native
end Arxiv2407_19026
