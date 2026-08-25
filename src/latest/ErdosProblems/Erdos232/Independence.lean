/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CombinatorialInt

namespace Erdos232

@[simp] theorem bitVec_zero_eq (s : BitVec 0) : s = 0#0 :=
  Subsingleton.elim _ _

/-- A mask is independent precisely when it contains no unit-distance edge of the
23-point certificate configuration. -/
def independentMaskBV (s : BitVec 23) : Bool :=
    !(s.getLsbD 0 && s.getLsbD 1) &&
    !(s.getLsbD 0 && s.getLsbD 2) &&
    !(s.getLsbD 0 && s.getLsbD 4) &&
    !(s.getLsbD 0 && s.getLsbD 5) &&
    !(s.getLsbD 0 && s.getLsbD 8) &&
    !(s.getLsbD 1 && s.getLsbD 2) &&
    !(s.getLsbD 1 && s.getLsbD 3) &&
    !(s.getLsbD 1 && s.getLsbD 11) &&
    !(s.getLsbD 1 && s.getLsbD 18) &&
    !(s.getLsbD 1 && s.getLsbD 19) &&
    !(s.getLsbD 2 && s.getLsbD 3) &&
    !(s.getLsbD 3 && s.getLsbD 6) &&
    !(s.getLsbD 3 && s.getLsbD 7) &&
    !(s.getLsbD 3 && s.getLsbD 10) &&
    !(s.getLsbD 4 && s.getLsbD 5) &&
    !(s.getLsbD 4 && s.getLsbD 6) &&
    !(s.getLsbD 4 && s.getLsbD 7) &&
    !(s.getLsbD 4 && s.getLsbD 9) &&
    !(s.getLsbD 4 && s.getLsbD 12) &&
    !(s.getLsbD 4 && s.getLsbD 17) &&
    !(s.getLsbD 5 && s.getLsbD 6) &&
    !(s.getLsbD 5 && s.getLsbD 10) &&
    !(s.getLsbD 5 && s.getLsbD 15) &&
    !(s.getLsbD 6 && s.getLsbD 18) &&
    !(s.getLsbD 7 && s.getLsbD 8) &&
    !(s.getLsbD 7 && s.getLsbD 9) &&
    !(s.getLsbD 7 && s.getLsbD 10) &&
    !(s.getLsbD 7 && s.getLsbD 13) &&
    !(s.getLsbD 8 && s.getLsbD 10) &&
    !(s.getLsbD 9 && s.getLsbD 11) &&
    !(s.getLsbD 9 && s.getLsbD 12) &&
    !(s.getLsbD 9 && s.getLsbD 14) &&
    !(s.getLsbD 9 && s.getLsbD 15) &&
    !(s.getLsbD 9 && s.getLsbD 16) &&
    !(s.getLsbD 10 && s.getLsbD 15) &&
    !(s.getLsbD 10 && s.getLsbD 20) &&
    !(s.getLsbD 11 && s.getLsbD 13) &&
    !(s.getLsbD 11 && s.getLsbD 14) &&
    !(s.getLsbD 11 && s.getLsbD 16) &&
    !(s.getLsbD 11 && s.getLsbD 17) &&
    !(s.getLsbD 12 && s.getLsbD 21) &&
    !(s.getLsbD 13 && s.getLsbD 17) &&
    !(s.getLsbD 16 && s.getLsbD 20) &&
    !(s.getLsbD 16 && s.getLsbD 21) &&
    !(s.getLsbD 16 && s.getLsbD 22) &&
    !(s.getLsbD 18 && s.getLsbD 19) &&
    !(s.getLsbD 21 && s.getLsbD 22)

end Erdos232
