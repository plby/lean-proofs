/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureStageGeometry
import ErdosProblems.Erdos599.HalfwayOldStageIntervalTransaction

/-!
# The finite interval row chosen after the Assertion 9.31 closure

The scheduled deletion-safe path is selected at the current club stage
before Claim 9.31 closes its vertex set.  After the dynamic closure chooses
a later club stage, the same path family is completed to a finite-character
linkage from the current frontier to that later frontier.

This file records that dependency order without identifying the two
frontiers and without reselecting the scheduled path after the closure.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.CardinalInduction

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- A deletion-safe singleton linkage at an explicit actual stage.
In particular its index may be zero; no preceding stage or membership
of that index in the avoiding club is implicit in this data. -/
structure SafeStageTargetPath
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (a : Ladder.Stage (succ kappa))
    (z : V) where
  stageFamily : Set (C.ladder.stageWeb a).DPath
  stage_linkage : IsLinkageBetween (C.ladder.stageWeb a)
    {z} (C.ladder.stageWeb a).target stageFamily
  deletion_safe :
    ((C.ladder.stageWeb a).delete ((C.ladder.stageWeb a).vertexSet stageFamily)).IsUnhindered
  ambientFamily : Set Gamma.DPath
  ambient_eq_lift : ambientFamily = SliceSegmentCore.liftStageFamily C.ladder a stageFamily
  ambient_linkage : IsLinkageBetween Gamma {z} Gamma.target ambientFamily

/-- A deletion-safe singleton linkage chosen at the current (new) stage of
`C`.  It is deliberately independent of any later stage. -/
structure SafeCurrentStageTargetPath
    (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (z : V) where
  stageFamily : Set (C.ladder.stageWeb C.newStage).DPath
  stage_linkage : IsLinkageBetween (C.ladder.stageWeb C.newStage)
    {z} (C.ladder.stageWeb C.newStage).target stageFamily
  deletion_safe :
    ((C.ladder.stageWeb C.newStage).delete
      ((C.ladder.stageWeb C.newStage).vertexSet stageFamily)).IsUnhindered
  ambientFamily : Set Gamma.DPath
  ambient_eq_lift : ambientFamily =
    SliceSegmentCore.liftStageFamily C.ladder C.newStage stageFamily
  ambient_linkage :
    IsLinkageBetween Gamma {z} Gamma.target ambientFamily

/-- Specialization preserves the old current-stage interface literally. -/
def SafeStageTargetPath.toCurrent
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {z : V}
    (P : SafeStageTargetPath C C.newStage z) : SafeCurrentStageTargetPath C z where
  stageFamily := P.stageFamily
  stage_linkage := P.stage_linkage
  deletion_safe := P.deletion_safe
  ambientFamily := P.ambientFamily
  ambient_eq_lift := P.ambient_eq_lift
  ambient_linkage := P.ambient_linkage

namespace SafeCurrentStageTargetPath

/-- Assertion 9.23 at the current stage, before a later stage is chosen. -/
theorem exists_of_mem_currentSlice
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {z : V} (hz : z ∈ C.newSlice) :
    Nonempty (SafeCurrentStageTargetPath C z) := by
  let H := C.ladder.stageWeb C.newStage
  obtain ⟨c⟩ := CardinalInduction.RegularSafeCompletion.exists_safeCompletionChoice
    H ∅ (by simpa [H] using C.newStage_isUnhindered) hz (by simp)
  let P : Set H.DPath := c.family
  have hP : IsLinkageBetween H {z} H.target P :=
    c.family_isLinkageBetween
  have hsafe : (H.delete (H.vertexSet P)).IsUnhindered := by
    rw [c.vertexSet_family]
    simpa only [empty_union] using c.next_unhindered
  let Q : Set Gamma.DPath :=
    SliceSegmentCore.liftStageFamily C.ladder C.newStage P
  have hQ : IsLinkageBetween Gamma {z} Gamma.target Q :=
    CardinalInduction.SliceDeltaLift.IsLinkageBetween.liftStageFamily hP
  exact ⟨{
    stageFamily := P
    stage_linkage := hP
    deletion_safe := hsafe
    ambientFamily := Q
    ambient_eq_lift := rfl
    ambient_linkage := hQ }⟩

/-- After the later club stage is captured, the already-selected current
stage family is literally the safe old-stage family for the rebased
geometry. -/
def toCaptured
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V} {z : V}
    (P : SafeCurrentStageTargetPath C z)
    (R : DynamicMoving931GlobalClosure C globalZ X0) :
    SafeOldStageTargetPath R.capturedGeometry z where
  stageFamily := P.stageFamily
  stage_linkage := P.stage_linkage
  deletion_safe := P.deletion_safe
  ambientFamily := P.ambientFamily
  ambient_eq_lift := P.ambient_eq_lift
  ambient_linkage := P.ambient_linkage

@[simp] theorem toCaptured_stageFamily
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V} {z : V}
    (P : SafeCurrentStageTargetPath C z)
    (R : DynamicMoving931GlobalClosure C globalZ X0) :
    (P.toCaptured R).stageFamily = P.stageFamily := rfl

@[simp] theorem toCaptured_ambientFamily
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    {globalZ X0 : Set V} {z : V}
    (P : SafeCurrentStageTargetPath C z)
    (R : DynamicMoving931GlobalClosure C globalZ X0) :
    (P.toCaptured R).ambientFamily = P.ambientFamily := rfl

end SafeCurrentStageTargetPath

/-- The actual finite linkage chosen after the dynamic closure.  The
scheduled safe path is the path chosen before closing, and its complete
ambient carrier belongs to the completed set. -/
structure PostClosureIntervalTransaction
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (globalZ X0 : Set V) (z : V)
    (R : DynamicMoving931GlobalClosure C globalZ X0) where
  safe : SafeCurrentStageTargetPath C z
  safe_seeded : Gamma.vertexSet safe.ambientFamily ⊆ X0
  safe_vertices_closed :
    Gamma.vertexSet safe.ambientFamily ⊆ R.closedSet
  interval : OldStageIntervalTransaction R.capturedGeometry z
  interval_safe_eq : interval.safe = safe.toCaptured R
  interval_reference_missing :
    IntervalReferenceMissingCertificate interval

namespace PostClosureIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ X0 : Set V} {z : V}
variable {R : DynamicMoving931GlobalClosure C globalZ X0}

/-- The literal finite interval reference at the captured pair of stages.
It is the ambient lift of the canonical deferred survivor intervals, so its
initials lie on the current frontier and its terminals lie on the captured
later frontier. -/
def intervalReference
    (T : PostClosureIntervalTransaction C globalZ X0 z R) :
    Set Gamma.DPath :=
  SliceSegmentCore.liftStageFamily R.capturedGeometry.ladder
    R.capturedGeometry.oldStage
    R.capturedGeometry.deferredOldStageOrdinaryFamily

theorem intervalReference_isLinkageBetween
    (T : PostClosureIntervalTransaction C globalZ X0 z R) :
    IsLinkageBetween Gamma
      (R.capturedGeometry.oldSlice \
        R.capturedGeometry.deferredOldStageExceptional)
      R.capturedGeometry.newSlice T.intervalReference := by
  exact _root_.Erdos599.CardinalInduction.SliceDeltaLift.IsLinkageBetween.liftStageFamily
    R.capturedGeometry.deferredOldStageOrdinaryFamily_isLinkageBetween

theorem intervalReference_initialSet_subset_currentSlice
    (T : PostClosureIntervalTransaction C globalZ X0 z R) :
    Gamma.initialSet T.intervalReference ⊆ C.newSlice := by
  rw [T.intervalReference_isLinkageBetween.initialSet_eq]
  simpa only [DynamicMoving931GlobalClosure.capturedGeometry_oldSlice] using
    (Set.sdiff_subset :
      R.capturedGeometry.oldSlice \
        R.capturedGeometry.deferredOldStageExceptional ⊆
          R.capturedGeometry.oldSlice)

/-- Exact path-level description of the missing side of the selected
interval reference.  This is the finite `H_beta` dependency in Claim 9.31,
not an abstract boundary premise. -/
theorem intervalReference_missing_member
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    {q : Gamma.DPath} (hqRef : q ∈ T.intervalReference)
    (hqMissing : q ∉ T.interval.ambientInterval) :
    q.initial ∈
        ((R.capturedGeometry.deferredOldStageExceptional ∪ {z}) ∪
          oldStageContactInitials R.capturedGeometry T.interval.safe) ∨
      q.support ⊆ T.interval.exceptionalComponents := by
  obtain ⟨p, hpRef, rfl⟩ := hqRef
  rcases T.interval_reference_missing.missing p hpRef hqMissing with
    hroot | hsupport
  · left
    simpa only [
      _root_.Erdos599.CardinalInduction.SliceSegmentCore.liftStagePath_initial]
      using hroot
  · right
    intro x hx
    apply hsupport
    simpa only [SliceSegmentCore.liftStagePath_support] using hx

/-- Set-level missing-carrier decomposition.  A moving symmetric-difference
closure only has to absorb the displayed root family and the already
constructed exceptional component; all other canonical survivor intervals
are literal members of the later row. -/
theorem intervalReference_sdiff_vertexSet_subset
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    (hrootPaths : ∀ p ∈ T.intervalReference,
      p.initial ∈
          ((R.capturedGeometry.deferredOldStageExceptional ∪ {z}) ∪
            oldStageContactInitials R.capturedGeometry T.interval.safe) →
        p.support ⊆ R.closedSet)
    (hcomponents : T.interval.exceptionalComponents ⊆ R.closedSet) :
    Gamma.vertexSet (T.intervalReference \ T.interval.ambientInterval) ⊆
      R.closedSet := by
  rintro x ⟨q, ⟨hqRef, hqMissing⟩, hxq⟩
  rcases T.intervalReference_missing_member hqRef hqMissing with
    hroot | hsupport
  · exact hrootPaths q hqRef hroot hxq
  · exact hcomponents (hsupport hxq)

end PostClosureIntervalTransaction

namespace DynamicMoving931GlobalClosure

/-- Complete the preselected and seeded path to the honest current-to-later
finite interval linkage.  No path is reselected after closing `X`. -/
theorem exists_postClosureIntervalTransaction
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {globalZ X0 : Set V} {z : V}
    (P : SafeCurrentStageTargetPath C z)
    (hPseed : Gamma.vertexSet P.ambientFamily ⊆ X0)
    (R : DynamicMoving931GlobalClosure C globalZ X0)
    (hz : z ∈ C.newSlice)
    (hext :
      _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
        Gamma kappa) :
    Nonempty (PostClosureIntervalTransaction C globalZ X0 z R) := by
  have hz' : z ∈ R.capturedGeometry.oldSlice := by
    simpa only [capturedGeometry_oldSlice] using hz
  obtain ⟨⟨T, hT⟩⟩ :=
    R.capturedGeometry.exists_oldStageIntervalTransaction_of_safe_extensionThrough
      hext (P.toCaptured R) hz'
  exact ⟨{
    safe := P
    safe_seeded := hPseed
    safe_vertices_closed := hPseed.trans R.seed_subset
    interval := T
    interval_safe_eq := hT.1
    interval_reference_missing := hT.2 }⟩

end DynamicMoving931GlobalClosure

#print axioms SafeCurrentStageTargetPath.exists_of_mem_currentSlice
#print axioms
  DynamicMoving931GlobalClosure.exists_postClosureIntervalTransaction
#print axioms PostClosureIntervalTransaction.intervalReference_isLinkageBetween
#print axioms PostClosureIntervalTransaction.intervalReference_missing_member
#print axioms
  PostClosureIntervalTransaction.intervalReference_sdiff_vertexSet_subset

end Erdos599.Blueprint.LinkageBlueprint
