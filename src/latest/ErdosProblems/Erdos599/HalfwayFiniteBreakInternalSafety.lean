/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteCoordinateInternalSafety
import ErdosProblems.Erdos599.HalfwayFiniteInputBreakInterval

/-!
# Internal safety of consecutive finite contact intervals

The canonical break interval is a coordinate restriction of the parent
compressor, so it inherits the exact backward-owner and no-ray/no-cycle
certificate proved for coordinate intervals.
-/

noncomputable section

open Set

namespace Erdos599.Blueprint

open DirectedPath _root_.Erdos599.Alternating

universe u w

variable {V : Type u} {Gamma : DWeb V}
variable {Y : Set Gamma.DPath} {I : Type w}

theorem InternallySafe.breakIntervalPath
    (S : RunCompressor.FiniteInput Gamma.graph)
    (X : Set V)
    (hparent : InternallySafe Y
      (.finite S.toFiniteRunWalk.toFiniteTrace))
    (P : (AltPath.finite S.toFiniteRunWalk.toFiniteTrace
      ).IndexedBackwardProvenance Y I)
    (i : Fin (S.finiteWalk.breakCount X)) :
    InternallySafe Y (S.breakIntervalPath X i) := by
  unfold RunCompressor.FiniteInput.breakIntervalPath
  exact hparent.coordinateInterval S
    (S.finiteWalk.breakPosition X i.castSucc)
    (S.finiteWalk.breakPosition X i.succ)
    (S.breakPosition_lt_succ X i)
    (by
      rw [← S.finiteWalk_finalPosition]
      exact S.finiteWalk.breakPosition_le_final X i.succ)
    P

end Erdos599.Blueprint

#print axioms Erdos599.Blueprint.InternallySafe.breakIntervalPath
