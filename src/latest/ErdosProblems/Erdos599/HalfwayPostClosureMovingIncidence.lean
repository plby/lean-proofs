/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureOldRoofIncidence
import ErdosProblems.Erdos599.HalfwayPostClosureMovingSuccessor

/-!
# Feeding actual post-closure incidence to the moving 9.31 compiler

The occurrence/contact construction and the relation assembler are kept
separate.  Once the assembler proves that its edge relation contains no
edges beyond the old blueprint and the literal actual post-closure edge set,
old-carrier predecessor preservation follows from the old-roof incidence
theorem.  All remaining Assertion 9.31 fields stay in the concrete
`AdvanceSpliceRelation`; no universal successor provider is introduced.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed currentClosed finalClosed B : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

namespace AdvanceSpliceRelation

/-- The exact final incidence adapter for the actual post-closure edge
decomposition.  The only relation-assembly input is the concrete containment
in the retained old edges plus `W[X]` and the occurrence-indexed segmented
outside edges.

The linkage-blueprint carrier bound is deliberately the independent
`finalClosed` parameter already certified by `R`.  In particular this lemma
does not identify it with the hammock-closing set `Rlimit.closedSet`: covered
forward intervals of the locally compiled assignment can leave that set. -/
theorem exists_fullyPredecessorPreservingMovingAdvance931_of_actualPostClosureEdges
    (A : PostClosureCompressorAssignment T)
    (ancestor current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (R : AdvanceSpliceRelation ancestor current z
      Rlimit.capturedGeometry.newSlice finalClosed C.persistent B)
    (hz : z ∈ C.newSlice)
    (hedges : R.edge ⊆
      current.edgeSet ∪ A.actualPostClosureFreshEdges) :
    ∃ U : LinkageBlueprint Gamma C.ladder.limitWarp kappa,
      MovingAdvance931 ancestor current U z C.newSlice
        Rlimit.capturedGeometry.newSlice finalClosed C.persistent B ∧
      current.NoNewPredecessorsTo U := by
  apply R.exists_fullyPredecessorPreservingMovingAdvance931_of_noIncomingOld hz
  intro x y hx hyx hyxOld
  apply hyxOld
  exact A.current_union_actualPostClosureFreshEdges_noNewIncoming
    current hcurrent hx (hedges hyx)

#print axioms
  exists_fullyPredecessorPreservingMovingAdvance931_of_actualPostClosureEdges

end AdvanceSpliceRelation
end Erdos599.Blueprint.LinkageBlueprint
