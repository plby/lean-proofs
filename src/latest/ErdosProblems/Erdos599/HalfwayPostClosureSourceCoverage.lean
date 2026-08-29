/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayRootedSourceCoverage
import ErdosProblems.Erdos599.HalfwayPostClosureSourceAbsorption

/-!
# Actual moving-frontier source coverage

The causal closing set already contains the reference difference between
the current and captured frontiers. Every needed source-prefix owner is
also wholly closed. Thus the source-cover transfer needs only the actual
prefix roots and the final carrier accounting, not an extra difference
closure or exact-frontier hypothesis.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V}

namespace LimitMoving931GlobalClosure

theorem lostReferenceOwners_meet_closedSet
    (R : LimitMoving931GlobalClosure C globalZ seed) :
    referencePathsMeeting C.ladder.limitWarp C.newSlice \
        referencePathsMeeting C.ladder.limitWarp R.capturedGeometry.newSlice ⊆
      referencePathsMeeting C.ladder.limitWarp R.closedSet := by
  intro p hp
  refine ⟨hp.1.1, p.initial, p.initial_mem_support, ?_⟩
  apply R.difference_subset
  exact ⟨p, Or.inl hp, p.initial_mem_support⟩

/-- Every source-prefix owner chosen by the actual diamond lies wholly in
the closing set, even if the original limiting owner is infinite. -/
theorem sourcePrefixOwner_support_closed
    (R : LimitMoving931GlobalClosure C globalZ seed)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {p : Gamma.DPath}
    (hp : p ∈ sourcePrefixOwners current C.newSlice R.closedSet) :
    p.support ⊆ R.closedSet :=
  R.reference_closed p hp.1.1.1 hp.1.2.2

/-- Source coverage for the actual captured frontier. The only new
construction-specific facts are the prefix initials and the exact carrier
accounting; the reference-difference premise has been discharged. -/
theorem covers_source_of_prefix_initials
    (R : LimitMoving931GlobalClosure C globalZ seed)
    (current U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint C.newSlice currentClosed C.persistent)
    (holdInitial : current.initialSet ⊆ U.initialSet)
    (hcarrier : U.vertexSet ⊆ current.vertexSet ∪ R.closedSet)
    (hprefix : Gamma.initialSet
      (sourcePrefixOwners current C.newSlice R.closedSet) ∩ Gamma.source ⊆ U.initialSet) :
    Gamma.source ⊆ U.initialSet ∪
      U.retainedReferenceInitials R.capturedGeometry.newSlice :=
  covers_source_of_source_referencePrefix_initials current U
    hcurrent.covers_source holdInitial hcarrier
    R.lostReferenceOwners_meet_closedSet hprefix

#print axioms lostReferenceOwners_meet_closedSet
#print axioms sourcePrefixOwner_support_closed
#print axioms covers_source_of_prefix_initials

end LimitMoving931GlobalClosure
end Erdos599.Blueprint.LinkageBlueprint
