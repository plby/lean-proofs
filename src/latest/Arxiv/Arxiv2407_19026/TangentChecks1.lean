import Arxiv.Arxiv2407_19026.TangentNumerics

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentRound1Native

open TangentAffine

def β0 : ℚ := 2 / 25
def β1 : ℚ := 9 / 200
def plateauT : Expr := c (99 / 100)

def forwardFine : List ℚ := fineBreakpoints 1000 1690
def forwardMedium : List ℚ := mediumBreakpoints 100 169
def plateauMedium : List ℚ := mediumBreakpoints 269 118
def back1Fine : List ℚ := fineBreakpoints 3870 2130
def back1Medium : List ℚ := mediumBreakpoints 387 213
def back2Fine : List ℚ := fineBreakpoints 6000 4000
def back2Medium : List ℚ := mediumBreakpoints 600 400

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma small_checks :
    checkLowerAffineCover (smallCoordSlope β0 β1) (1 / 20)
        cfg 0 bpsSlope = true ∧
      checkLowerAffineCover (smallBookSlope β0 β1) (1 / 1000)
        cfg 0 bpsBookSlope = true ∧
      checkLowerAffineCover (smallBook β0 β1) (1 / 10000)
        cfg (1 / 50) bpsBook = true := by
  constructor
  · native_decide
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma back1_checks :
    checkLowerAffineCover (backwardLogCoord β0 β1 r1Back1T) 0
        cfg (387 / 1000) back1Fine = true ∧
      checkLowerAffineCover (backwardBook β0 β1 r1Back1T)
        (1 / 1000000) cfg (387 / 1000) back1Medium = true := by
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma back2_checks :
    checkLowerAffineCover (backwardLogCoord β0 β1 r1Back2T) 0
        cfg (3 / 5) back2Fine = true ∧
      checkLowerAffineCover (backwardBook β0 β1 r1Back2T)
        (1 / 1000000) cfg (3 / 5) back2Medium = true := by
  constructor <;> native_decide

end TangentRound1Native
end Arxiv2407_19026
