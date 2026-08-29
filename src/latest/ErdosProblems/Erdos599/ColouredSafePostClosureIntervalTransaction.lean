/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeMovingLimit
import ErdosProblems.Erdos599.HalfwayPostClosureIntervalTransaction

/-!
# The finite interval transaction over the native moving closure

This is the native-occurrence counterpart of `PostClosureIntervalTransaction`.
It is built directly from `ColouredSafeMovingStages.LimitClosure`; in
particular it does not coerce native hammock closure into the older
alternating-path closure record.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.CardinalInduction
open ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Re-index the ladder geometry at the later club stage selected by the
native moving closure. -/
def nativeCapturedGeometry
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {seed : Set V}
    (R : LimitClosure C seed) :
    ClubStageGeometry Gamma Y kappa (succ kappa) where
  ladder := C.ladder
  legal := C.legal
  hindranceRungs := C.hindranceRungs
  hindranceObstruction := C.hindranceObstruction
  normalized := C.normalized
  club := C.club
  club_isClub := C.club_isClub
  club_avoids_phi := C.club_avoids_phi
  oldStage := C.newStage
  newStage := R.later.stage
  old_mem_club := C.new_mem_club
  new_mem_club := R.later.mem_club
  old_lt_new := R.later.current_lt
  closedStage := fun _ => R.closedSet
  closedStage_mono := by
    intro a b hab x hx
    exact hx
  before_card := by
    apply (Cardinal.mk_subtype_mono ?_).trans R.card_le
    intro x hx
    obtain ⟨a, ha, hxa⟩ := hx
    exact hxa
  capacity_infinite := C.capacity_infinite

@[simp] theorem nativeCapturedGeometry_ladder
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {seed : Set V}
    (R : LimitClosure C seed) : (nativeCapturedGeometry R).ladder = C.ladder := rfl

@[simp] theorem nativeCapturedGeometry_oldStage
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {seed : Set V}
    (R : LimitClosure C seed) : (nativeCapturedGeometry R).oldStage = C.newStage := rfl

@[simp] theorem nativeCapturedGeometry_newStage
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {seed : Set V}
    (R : LimitClosure C seed) : (nativeCapturedGeometry R).newStage = R.later.stage := rfl

@[simp] theorem nativeCapturedGeometry_closedSet
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {seed : Set V}
    (R : LimitClosure C seed) : (nativeCapturedGeometry R).closedSet = R.closedSet := rfl

@[simp] theorem nativeCapturedGeometry_before
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {seed : Set V}
    (R : LimitClosure C seed) : (nativeCapturedGeometry R).before = R.closedSet := by
  change closedBefore (fun _ => R.closedSet) R.later.stage = R.closedSet
  ext x
  constructor
  · rintro ⟨a, ha, hxa⟩
    exact hxa
  · intro hx
    exact ⟨C.newStage, R.later.current_lt, hx⟩

@[simp] theorem nativeCapturedGeometry_oldSlice
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {seed : Set V}
    (R : LimitClosure C seed) : (nativeCapturedGeometry R).oldSlice = C.newSlice := rfl

@[simp] theorem nativeCapturedGeometry_newSlice
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {seed : Set V}
    (R : LimitClosure C seed) :
    (nativeCapturedGeometry R).newSlice = C.ladder.frontier R.later.stage := rfl

theorem nativeCapturedGeometry_closedSet_subset_newRoof
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {seed : Set V}
    (R : LimitClosure C seed) :
    (nativeCapturedGeometry R).closedSet ⊆
      (nativeCapturedGeometry R).outerRoof := by
  change R.closedSet ⊆ Gamma.roof (C.ladder.frontier R.later.stage)
  exact R.later.subset_roof

namespace SafeCurrentStageTargetPath

/-- Retype the path selected at the current stage into the geometry captured
by a native moving closure. -/
def toNativeCaptured
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {seed : Set V}
    {z : V} (P : SafeCurrentStageTargetPath C z)
    (R : LimitClosure C seed) :
    SafeOldStageTargetPath (nativeCapturedGeometry R) z where
  stageFamily := P.stageFamily
  stage_linkage := P.stage_linkage
  deletion_safe := P.deletion_safe
  ambientFamily := P.ambientFamily
  ambient_eq_lift := P.ambient_eq_lift
  ambient_linkage := P.ambient_linkage

@[simp] theorem toNativeCaptured_stageFamily
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {seed : Set V}
    {z : V} (P : SafeCurrentStageTargetPath C z) (R : LimitClosure C seed) :
    (P.toNativeCaptured R).stageFamily = P.stageFamily := rfl

@[simp] theorem toNativeCaptured_ambientFamily
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {seed : Set V}
    {z : V} (P : SafeCurrentStageTargetPath C z) (R : LimitClosure C seed) :
    (P.toNativeCaptured R).ambientFamily = P.ambientFamily := rfl

end SafeCurrentStageTargetPath

/-- The honest current-to-later finite interval row constructed over a
native occurrence closure. -/
structure NativePostClosureIntervalTransaction
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (seed : Set V) (z : V) (R : LimitClosure C seed) where
  safe : SafeCurrentStageTargetPath C z
  safe_seeded : Gamma.vertexSet safe.ambientFamily ⊆ seed
  safe_vertices_closed : Gamma.vertexSet safe.ambientFamily ⊆ R.closedSet
  interval : OldStageIntervalTransaction (nativeCapturedGeometry R) z
  interval_safe_eq : interval.safe = safe.toNativeCaptured R
  interval_reference_missing : IntervalReferenceMissingCertificate interval

namespace NativePostClosureIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}

/-- The literal deferred survivor intervals between the current and native
captured later stage. -/
def intervalReference (T : NativePostClosureIntervalTransaction C seed z R) :
    Set Gamma.DPath :=
  SliceSegmentCore.liftStageFamily (nativeCapturedGeometry R).ladder
    (nativeCapturedGeometry R).oldStage
    (nativeCapturedGeometry R).deferredOldStageOrdinaryFamily

theorem intervalReference_isLinkageBetween
    (T : NativePostClosureIntervalTransaction C seed z R) :
    IsLinkageBetween Gamma
      ((nativeCapturedGeometry R).oldSlice \
        (nativeCapturedGeometry R).deferredOldStageExceptional)
      (nativeCapturedGeometry R).newSlice T.intervalReference :=
  _root_.Erdos599.CardinalInduction.SliceDeltaLift.IsLinkageBetween.liftStageFamily
    (nativeCapturedGeometry R).deferredOldStageOrdinaryFamily_isLinkageBetween

theorem intervalReference_initialSet_subset_currentSlice
    (T : NativePostClosureIntervalTransaction C seed z R) :
    Gamma.initialSet T.intervalReference ⊆ C.newSlice := by
  rw [T.intervalReference_isLinkageBetween.initialSet_eq]
  simpa only [nativeCapturedGeometry_oldSlice] using
    (Set.sdiff_subset :
      (nativeCapturedGeometry R).oldSlice \
        (nativeCapturedGeometry R).deferredOldStageExceptional ⊆
          (nativeCapturedGeometry R).oldSlice)

end NativePostClosureIntervalTransaction

namespace NativePostClosureIntervalTransaction

/-- Complete a preselected and seeded current-stage path to the native
current-to-later interval transaction. -/
theorem exists_nativePostClosureIntervalTransaction
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {seed : Set V} {z : V}
    (P : SafeCurrentStageTargetPath C z)
    (hPseed : Gamma.vertexSet P.ambientFamily ⊆ seed)
    (R : LimitClosure C seed) (hz : z ∈ C.newSlice)
    (hext :
      _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
        Gamma kappa) :
    Nonempty (NativePostClosureIntervalTransaction C seed z R) := by
  have hz' : z ∈ (nativeCapturedGeometry R).oldSlice := by
    simpa only [nativeCapturedGeometry_oldSlice] using hz
  obtain ⟨⟨T, hT⟩⟩ :=
    (nativeCapturedGeometry R).exists_oldStageIntervalTransaction_of_safe_extensionThrough
      hext (P.toNativeCaptured R) hz'
  exact ⟨{
    safe := P
    safe_seeded := hPseed
    safe_vertices_closed := hPseed.trans R.seed_subset
    interval := T
    interval_safe_eq := hT.1
    interval_reference_missing := hT.2 }⟩

end NativePostClosureIntervalTransaction

#print axioms nativeCapturedGeometry_before
#print axioms
  NativePostClosureIntervalTransaction.exists_nativePostClosureIntervalTransaction
#print axioms NativePostClosureIntervalTransaction.intervalReference_isLinkageBetween

end Erdos599.Blueprint.LinkageBlueprint
