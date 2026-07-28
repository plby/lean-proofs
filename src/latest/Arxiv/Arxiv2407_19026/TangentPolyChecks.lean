import Arxiv.Arxiv2407_19026.TangentPolynomialBounds

open LeanCert.Core LeanCert.Engine LeanCert.Validity

namespace Arxiv2407_19026
namespace TangentPolyNative

open TangentAffine

def r1ForwardBps : List ℚ := mediumBreakpoints 100 169
def r1Back1Bps : List ℚ := mediumBreakpoints 387 213
def r2ForwardBps : List ℚ := mediumBreakpoints 100 168
def r2Back1Bps : List ℚ := mediumBreakpoints 378 222
def r3ForwardBps : List ℚ := mediumBreakpoints 100 168
def r3Back1Bps : List ℚ := mediumBreakpoints 375 225
def back2Bps : List ℚ := mediumBreakpoints 600 400

def belowOne (T : Expr) : Expr := sub (c 1) T

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma r1Forward_checks :
    checkLowerAffineCover r1ForwardT (1 / 100000)
        cfg (1 / 10) r1ForwardBps = true ∧
      checkLowerAffineCover (belowOne r1ForwardT) (1 / 100000)
        cfg (1 / 10) r1ForwardBps = true := by
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma r1Back1_checks :
    checkLowerAffineCover r1Back1T (1 / 100000)
        cfg (387 / 1000) r1Back1Bps = true ∧
      checkLowerAffineCover (belowOne r1Back1T) (1 / 100000)
        cfg (387 / 1000) r1Back1Bps = true := by
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma r1Back2_checks :
    checkLowerAffineCover r1Back2T (1 / 100000)
        cfg (3 / 5) back2Bps = true ∧
      checkLowerAffineCover (belowOne r1Back2T) (1 / 100000)
        cfg (3 / 5) back2Bps = true := by
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma r2Forward_checks :
    checkLowerAffineCover r2ForwardT (1 / 100000)
        cfg (1 / 10) r2ForwardBps = true ∧
      checkLowerAffineCover (belowOne r2ForwardT) (1 / 100000)
        cfg (1 / 10) r2ForwardBps = true := by
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma r2Back1_checks :
    checkLowerAffineCover r2Back1T (1 / 100000)
        cfg (189 / 500) r2Back1Bps = true ∧
      checkLowerAffineCover (belowOne r2Back1T) (1 / 100000)
        cfg (189 / 500) r2Back1Bps = true := by
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma r2Back2_checks :
    checkLowerAffineCover r2Back2T (1 / 100000)
        cfg (3 / 5) back2Bps = true ∧
      checkLowerAffineCover (belowOne r2Back2T) (1 / 100000)
        cfg (3 / 5) back2Bps = true := by
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma r3Forward_checks :
    checkLowerAffineCover r3ForwardT (1 / 100000)
        cfg (1 / 10) r3ForwardBps = true ∧
      checkLowerAffineCover (belowOne r3ForwardT) (1 / 100000)
        cfg (1 / 10) r3ForwardBps = true := by
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma r3Back1_checks :
    checkLowerAffineCover r3Back1T (1 / 100000)
        cfg (3 / 8) r3Back1Bps = true ∧
      checkLowerAffineCover (belowOne r3Back1T) (1 / 100000)
        cfg (3 / 8) r3Back1Bps = true := by
  constructor <;> native_decide

set_option maxHeartbeats 0 in
-- The finite rational-grid certificate requires an unbounded heartbeat budget.
lemma r3Back2_checks :
    checkLowerAffineCover r3Back2T (1 / 100000)
        cfg (3 / 5) back2Bps = true ∧
      checkLowerAffineCover (belowOne r3Back2T) (1 / 100000)
        cfg (3 / 5) back2Bps = true := by
  constructor <;> native_decide

end TangentPolyNative
end Arxiv2407_19026
