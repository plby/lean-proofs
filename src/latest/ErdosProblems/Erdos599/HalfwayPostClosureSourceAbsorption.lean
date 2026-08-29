/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureContactEligibility
import ErdosProblems.Erdos599.DeferredCurrentRecordRoof

/-!
# Actual uncovered hole initials belong to the closing set

An old-frontier nonsurvivor extends to an inessential component at the later
stage.  This component is already a literal limiting member, hits the old
frontier and misses the later one.  Thus its old terminal lies in the moving
symmetric difference, which the closure absorbed before choosing the row.

Every other old initial lies on a canonical survivor interval.  Global
reference closure implies that such an interval with initial outside the
closing set is wholly outside it, so that initial is already covered by the
outside reference and cannot be a source of the fractured assignment.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open _root_.Erdos599.DirectedPath _root_.Erdos599.Alternating Ladder
open _root_.Erdos599.CardinalInduction

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClubStageGeometry

/-- All old nonsurvivor sources lie on global members which hit the old
frontier and miss the later frontier. -/
theorem nonsurvivorSources_subset_movingReferenceDifference
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (a b : Ladder.Stage (succ kappa)) (hab : a ≤ b) :
    RegularSliceSurvivors.nonsurvivorSources Gamma C.ladder a b ⊆
      C.movingReferenceDifference a b := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ :=
    Gamma.exists_essentialWarpPart_terminal_of_mem_quotientEssentialPart_source
      (C.legal.roofsSourceAtStages (Ladder.Stage.toExtended a)) hx.1
  rcases p with p | r
  swap
  · simp at hpx
  obtain ⟨q, hq, hpq⟩ := DeferredStageInterval.warpAt_grows_of_le C.legal hab
    (.inl p) hp.1
  have hqIE : q ∈ Gamma.inessentialPaths (C.ladder.warpAt b) := by
    refine ⟨hq, ?_⟩
    intro hqEssential
    rcases q with q | r
    · exact hx.2 ⟨hx.1, p, q, hp, hqEssential, Option.some.inj hpx, hpq⟩
    · obtain ⟨_, t, ht, _⟩ := hqEssential
      simp at ht
  have hqGlobal := C.legal.mem_limitWarp_of_mem_inessential hqIE
  have hxp : x ∈ Path.support (Sum.inl p : Gamma.DPath) :=
    Gamma.terminal_mem_support hpx
  have hxq : x ∈ q.support := Gamma.support_mono_of_extends hpq hxp
  have hqA : q ∈ C.limitReferenceAtFrontier a := ⟨hqGlobal, x, hxq, hx.1⟩
  have hqNotB : q ∉ C.limitReferenceAtFrontier b := by
    rintro ⟨_hq, y, hyq, hyB⟩
    have hyStrict :=
      DWeb.KappaLadder.Deferred.inessentialPath_support_subset_strictRoof_frontier
        C.ladder C.legal hqIE hyq
    apply hyStrict.2
    rwa [C.legal.frontiersEssential b]
  exact ⟨q, Or.inl ⟨hqA, hqNotB⟩, hxq⟩

end ClubStageGeometry

namespace PostClosureIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}

/-- The genuine nonsurvivor roots, unlike the residual completion chosen
later, are already absorbed by the moving symmetric-difference closure. -/
theorem deferredExceptional_subset_closedSet
    (R : LimitMoving931GlobalClosure C globalZ seed) :
    R.toDynamicMoving931GlobalClosure.capturedGeometry.deferredOldStageExceptional ⊆
      R.closedSet := by
  change RegularSliceSurvivors.nonsurvivorSources Gamma C.ladder
    C.newStage R.later.stage ⊆ R.closedSet
  exact (C.nonsurvivorSources_subset_movingReferenceDifference C.newStage
    R.later.stage R.later.current_lt.le).trans R.difference_subset

/-- Global path closure descends to the canonical subinterval reference. -/
theorem intervalReference_closedUnderPaths
    {R : DynamicMoving931GlobalClosure C globalZ seed}
    (T : PostClosureIntervalTransaction C globalZ seed z R) :
    ClosedUnderPaths Gamma T.intervalReference R.closedSet := by
  intro q hq hmeet
  let qs : T.intervalReference := ⟨q, hq⟩
  obtain ⟨x, hxq, hxX⟩ := hmeet
  have howner := R.reference_closed (T.intervalReferenceOwner qs)
    (T.intervalReferenceOwner_mem qs)
    ⟨x, (T.intervalReference_subpath_owner qs).1 hxq, hxX⟩
  exact (T.intervalReference_subpath_owner qs).1.trans howner

/-- An interval whose initial is outside the closed set is an actual
member of the outside reference. -/
theorem intervalReference_mem_outside_of_initial_not_mem
    {R : DynamicMoving931GlobalClosure C globalZ seed}
    (T : PostClosureIntervalTransaction C globalZ seed z R)
    {q : Gamma.DPath} (hq : q ∈ T.intervalReference)
    (hqx : q.initial ∉ R.closedSet) :
    q ∈ outsideReference T.intervalReference R.closedSet := by
  refine ⟨hq, Set.disjoint_left.mpr ?_⟩
  intro x hxq hxX
  exact hqx (T.intervalReference_closedUnderPaths q hq
    ⟨x, hxq, hxX⟩ q.initial_mem_support)

/-- Every source of the actual fractured assignment lies in the closing
set, even though the interval linkage is chosen after that set. -/
theorem uncovered_initials_subset_closedSet
    (R : LimitMoving931GlobalClosure C globalZ seed)
    (T : PostClosureIntervalTransaction C globalZ seed z
      R.toDynamicMoving931GlobalClosure)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet) :
    Gamma.initialSet F.outside.holes.paths \
        Gamma.initialSet (outsideReference T.intervalReference R.closedSet) ⊆
      R.closedSet := by
  intro x hx
  by_contra hxNotX
  have hxCut := hx.1
  rw [F.outside.initialSet_eq] at hxCut
  have hxW : x ∈ Gamma.initialSet T.interval.ambientInterval :=
    cutInitial_sdiff_subset_initialSet T.interval.ambientInterval_linkage.isWarp
      ⟨hxCut, hxNotX⟩
  have hxOld : x ∈ R.toDynamicMoving931GlobalClosure.capturedGeometry.oldSlice := by
    rwa [T.interval.ambientInterval_linkage.initialSet_eq] at hxW
  have hxReference : x ∈ Gamma.initialSet T.intervalReference := by
    rw [T.intervalReference_isLinkageBetween.initialSet_eq]
    exact ⟨hxOld, fun hxe ↦ hxNotX (deferredExceptional_subset_closedSet R hxe)⟩
  obtain ⟨q, hq, hqInitial⟩ := hxReference
  apply hx.2
  refine ⟨q, T.intervalReference_mem_outside_of_initial_not_mem hq ?_, hqInitial⟩
  rwa [hqInitial]

end PostClosureIntervalTransaction

#print axioms ClubStageGeometry.nonsurvivorSources_subset_movingReferenceDifference
#print axioms PostClosureIntervalTransaction.uncovered_initials_subset_closedSet

end Erdos599.Blueprint.LinkageBlueprint
