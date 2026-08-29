/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMovingBetaSequence
import ErdosProblems.Erdos599.HalfwayMovingReferenceReservoir

/-!
# Moving Claim 9.31 closure from the actual ladder history

This bridge removes the opaque hypothesis that every moving symmetric
difference is already in the global closing set.  The paper's causal
invariants suffice: every selected record is inserted, every marker is
inserted, and the global set is closed under the limiting reference.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace MovingBetaOmegaClosure

/-- Construct the source's countable moving closure from the concrete
record/marker invariants of the fixed global set. -/
theorem exists_of_recorded_marker_reservoir
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ seed : Set V)
    (hGlobalRoof : globalZ ⊆ C.ladder.limitRoof)
    (hGlobalHammocks : HammockClosedUpTo Gamma C.ladder.limitWarp
      globalZ globalZ C.ladder.limitStrictRoof C.ladder.limitRoof kappa)
    (hGlobalReferenceClosed :
      ClosedUnderPaths Gamma C.ladder.limitWarp globalZ)
    (hRecorded : ∀ (a : Ladder.Stage (succ kappa)) (p : Gamma.DPath),
      C.ladder.chosen a = some p → p.support ⊆ globalZ)
    (hMarkers : C.ladder.markerSet ⊆ globalZ)
    (hseedGlobal : seed ⊆ globalZ)
    (hseedCard : #seed ≤ kappa) :
    Nonempty (MovingBetaOmegaClosure C globalZ seed
      (fun b ↦ C.movingReferenceDifference C.newStage b)) := by
  apply exists_for_movingReferenceDifference C globalZ seed
    hGlobalRoof hGlobalHammocks hGlobalReferenceClosed
      hseedGlobal hseedCard
  exact C.movingReferenceDifference_subset_of_recorded_marker_closed
    hRecorded hMarkers hGlobalReferenceClosed

end MovingBetaOmegaClosure

#print axioms
  MovingBetaOmegaClosure.exists_of_recorded_marker_reservoir

end Erdos599.Blueprint.LinkageBlueprint

