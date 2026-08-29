/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureCompressorAssignment
import ErdosProblems.Erdos599.HalfwayFiniteBreakInternalSafety

/-!
# Actual finite post-closure contact intervals are internally safe

The post-closure producer supplies both global internal safety and indexed
global backward owners for the assigned trace.  In the finite compressor
branch these data restrict to every canonical contact interval.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment

open _root_.Erdos599.DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ X0 : Set V} {z : V}
variable {R : DynamicMoving931GlobalClosure C globalZ X0}
variable {T : PostClosureIntervalTransaction C globalZ X0 z R}

/-- In a finite realization of an actual assigned trace, every consecutive
contact interval is internally safe for the global limiting reference. -/
theorem finite_breakInterval_internallySafe
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference R.closedSet)})
    (S : RunCompressor.FiniteInput Gamma.graph)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .finite S.toFiniteRunWalk.toFiniteTrace)
    (i : Fin (S.finiteWalk.breakCount R.closedSet)) :
    InternallySafe C.ladder.limitWarp
      (S.breakIntervalPath R.closedSet i) := by
  have hparent : InternallySafe C.ladder.limitWarp
      (.finite S.toFiniteRunWalk.toFiniteTrace) := by
    rw [← hS]
    exact A.toPostClosureProducedAssignment.assigned_internallySafe_global s
  let H := A.toPostClosureProducedAssignment.assigned_backward_global s
  let I : Type u := H.Index
  have hP :
      (A.assignment.produced.bracket.assignment.assigned s
        ).IndexedBackwardProvenance C.ladder.limitWarp I := H.certificate
  have P : (AltPath.finite S.toFiniteRunWalk.toFiniteTrace
      ).IndexedBackwardProvenance C.ladder.limitWarp I := hS ▸ hP
  exact hparent.breakIntervalPath S R.closedSet P i

end Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment

#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment.finite_breakInterval_internallySafe
