/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderHangingProvenance
import ErdosProblems.Erdos599.LadderSuccessorBridge

/-!
# Deferred current-marker bookkeeping

The original successor-normalized choice family includes the marker path
inserted at the same stage.  That permits a selected hanging path to have its
origin at the current marker, whereas the pressing-down argument needs a
strictly earlier origin.  This module gives the minimal local repair: omit
paths whose initial is the current marker from the selectable family.  Such a
path remains in the accumulated warp and can be selected at a later stage.

`IsDeferredLegal` records the resulting fully proved construction laws.  It
is intentionally separate from `KappaLadder.IsLegal`: the latter's
`HasValidBookkeeping` field is definitionally tied to the unfiltered
successor-inessential family, so changing only a constructor cannot inhabit
that old field when the current marker is the sole inessential path.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- The successor-inessential paths selectable at `a`, omitting all paths
whose initial is the marker born at `a`. -/
def selectable (L : G.KappaLadder kappa)
    (a : Ladder.Stage kappa) : Set G.DPath :=
  {p | p ∈ G.inessentialPaths (L.successorWarp a) ∧
    L.marker a ≠ some p.initial}

@[simp]
theorem mem_selectable {L : G.KappaLadder kappa}
    {a : Ladder.Stage kappa} {p : G.DPath} :
    p ∈ selectable L a ↔
      p ∈ G.inessentialPaths (L.successorWarp a) ∧
        L.marker a ≠ some p.initial :=
  Iff.rfl

/-- A valid independent ray-preferring choice on the deferred selectable
families. -/
noncomputable def chosenBookkeeping (L : G.KappaLadder kappa) :
    Ladder.Bookkeeping kappa G.DPath :=
  Ladder.Bookkeeping.ofData
    (fun a : Ladder.Stage kappa ↦ selectable L a)
    (fun p : G.DPath ↦ G.terminal? p = none)

theorem chosenBookkeeping_spec (L : G.KappaLadder kappa) :
    (chosenBookkeeping L).inessentialNext =
        (fun a : Ladder.Stage kappa ↦ selectable L a) ∧
      (chosenBookkeeping L).isRay =
        (fun p : G.DPath ↦ G.terminal? p = none) ∧
      (chosenBookkeeping L).IsValid :=
  ⟨rfl, rfl, Ladder.Bookkeeping.ofData_isValid
    (fun a : Ladder.Stage kappa ↦ selectable L a)
    (fun p : G.DPath ↦ G.terminal? p = none)⟩

/-- Deferred record selection is prefix-causal once the selectable
families agree through the queried stage. -/
theorem chosenBookkeeping_chosen_congr_le
    (L M : G.KappaLadder kappa) (a : Ladder.Stage kappa)
    (hselectable : ∀ b, b ≤ a → selectable L b = selectable M b) :
    (chosenBookkeeping L).chosen a =
      (chosenBookkeeping M).chosen a := by
  unfold chosenBookkeeping
  exact Ladder.Bookkeeping.ofData_chosen_congr_le
    (fun b : Ladder.Stage kappa ↦ selectable L b)
    (fun b : Ladder.Stage kappa ↦ selectable M b)
    (fun p : G.DPath ↦ G.terminal? p = none) a hselectable

/-- Install deferred bookkeeping without changing ladder geometry. -/
noncomputable def withValidBookkeeping (L : G.KappaLadder kappa) :
    G.KappaLadder kappa where
  accumulated := L.accumulated
  rung := L.rung
  marker := L.marker
  chosen := (chosenBookkeeping L).chosen

/-- The deferred bookkeeping exposed independently of the legacy ladder
bookkeeping projection. -/
def bookkeeping (L : G.KappaLadder kappa) :
    Ladder.Bookkeeping kappa G.DPath where
  inessentialNext := fun a ↦ selectable L a
  isRay := fun p ↦ G.terminal? p = none
  chosen := L.chosen

def HasValidBookkeeping (L : G.KappaLadder kappa) : Prop :=
  (bookkeeping L).IsValid

theorem withValidBookkeeping_hasValidBookkeeping
    (L : G.KappaLadder kappa) :
    HasValidBookkeeping (withValidBookkeeping L) := by
  have hspec := chosenBookkeeping_spec L
  have heq : bookkeeping (withValidBookkeeping L) = chosenBookkeeping L := by
    cases hB : chosenBookkeeping L with
    | mk next ray chosen =>
      have hnext := hspec.1
      have hray := hspec.2.1
      rw [hB] at hnext hray
      change next = (fun a : Ladder.Stage kappa ↦ selectable L a) at hnext
      change ray = (fun p : G.DPath ↦ G.terminal? p = none) at hray
      subst next
      subst ray
      simp [bookkeeping, withValidBookkeeping, hB]
      rfl
  change (bookkeeping (withValidBookkeeping L)).IsValid
  rw [heq]
  exact hspec.2.2

/-- The canonical ladder with deferred current-marker bookkeeping. -/
noncomputable abbrev canonicalDeferredLadder
    (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Ladder.Stage kappa → Option V) : G.KappaLadder kappa :=
  withValidBookkeeping (G.canonicalLadderCore kappa preferred)

/-- Deferred validity implies that every selected path is successor
inessential and avoids the marker born at its selection stage. -/
theorem chosen_spec
    {L : G.KappaLadder kappa} (hL : HasValidBookkeeping L)
    {a : Ladder.Stage kappa} {p : G.DPath}
    (hp : L.chosen a = some p) :
    p ∈ G.inessentialPaths (L.successorWarp a) ∧
      L.marker a ≠ some p.initial := by
  exact ((bookkeeping L).chosen_mem_available hL hp).1

/-- Deferred records have strictly earlier marker provenance whenever they
are hanging. -/
theorem canonicalDeferredLadder_hasHangingProvenance
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (canonicalDeferredLadder G kappa preferred).HasHangingProvenance := by
  let L := canonicalDeferredLadder G kappa preferred
  have hvalid : HasValidBookkeeping L :=
    withValidBookkeeping_hasValidBookkeeping
      (G.canonicalLadderCore kappa preferred)
  have hprovenance : L.HasAccumulatedInitialProvenance := by
    change (canonicalLadder G kappa preferred).HasAccumulatedInitialProvenance
    exact canonicalLadder_hasAccumulatedInitialProvenance preferred hNoEnter
  intro a ha p hp
  have hpSpec := chosen_spec hvalid hp
  rcases hprovenance (Ladder.Stage.succExtended a) p hpSpec.1.1 with
      hpSource | ⟨b, hba, hb⟩
  · exact (ha.2 ⟨p, hp, hpSource⟩).elim
  · refine ⟨b, ?_, hb⟩
    have hble : b ≤ a := by
      change b.1 + 1 ≤ a.1 + 1 at hba
      change b.1 ≤ a.1
      rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one] at hba
      exact (Order.succ_le_succ_iff).1 hba
    rcases hble.lt_or_eq with hlt | heq
    · exact hlt
    · subst b
      exact (hpSpec.2 hb).elim

/-- The selected deferred records satisfy the same successor-and-limit
persistence conclusion as the original bookkeeping. -/
theorem canonicalDeferredLadder_recordedPathsPersist
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (canonicalDeferredLadder G kappa preferred).RecordedPathsPersist := by
  let L := canonicalDeferredLadder G kappa preferred
  have hvalid : HasValidBookkeeping L :=
    withValidBookkeeping_hasValidBookkeeping
      (G.canonicalLadderCore kappa preferred)
  intro a p hp b hab
  have hpNext : p ∈ G.inessentialPaths (L.successorWarp a) :=
    (chosen_spec hvalid hp).1
  change p ∈ G.inessentialPaths
    (G.canonicalLadderAccumulated kappa preferred b)
  exact canonicalAccumulated_inessential_mono
    preferred hNoEnter hab hpNext

/-- Source-faithful ladder legality with deferred bookkeeping.  The fields
are the construction laws of `KappaLadder.IsLegal`, with its legacy
bookkeeping-validity field replaced by deferred validity. -/
structure IsDeferredLegal (L : G.KappaLadder kappa) : Prop where
  regular : kappa.IsRegular
  uncountable : Cardinal.aleph0 < kappa
  initialStage : L.HasInitialStage
  limitStages : L.HasLimitStages
  warpStages : L.HasWarpStages
  waveRungs : L.HasWaveRungs
  roofMaximalRungs : L.HasRoofMaximalRungs
  exactSuccessorArrows : L.HasExactSuccessorArrows
  freshMarkers : L.HasFreshMarkers
  markersInjective : L.MarkersInjective
  marksTime : L.MarksTimeAfterExhaustion
  accumulatedInitialProvenance : L.HasAccumulatedInitialProvenance
  validBookkeeping : HasValidBookkeeping L
  hangingProvenance : L.HasHangingProvenance
  recordedPathsPersist : L.RecordedPathsPersist
  currentInessentialPersists : L.CurrentInessentialPersists
  roofsSourceAtStages : L.RoofsSourceAtStages
  frontiersEssential : L.FrontiersAreEssential
  frontierChronology : L.HasFrontierChronology
  strictFrontierChronology : L.HasStrictFrontierChronology

/-- Short namespace-qualified name for the repaired legality package. -/
abbrev IsLegal (L : G.KappaLadder kappa) : Prop := IsDeferredLegal L

/-- The repaired canonical construction is unconditionally deferred-legal
and retains maximal rungs. -/
theorem canonicalDeferredLadder_isDeferredLegal
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular)
    (hkappaUncountable : Cardinal.aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source) :
    IsDeferredLegal (canonicalDeferredLadder G kappa preferred) := by
  let L₀ := G.canonicalLadderCore kappa preferred
  let L := canonicalDeferredLadder G kappa preferred
  let Lold := canonicalLadder G kappa preferred
  have hgeometry : CanonicalLadderGeometry Lold :=
    canonicalLadder_geometry preferred hNoEnter
  have hsame : L.accumulated = Lold.accumulated := rfl
  have hsameRung : L.rung = Lold.rung := rfl
  have hsameMarker : L.marker = Lold.marker := rfl
  have hinitial : L.HasInitialStage := by
    change (G.canonicalLadderCore kappa preferred).HasInitialStage
    exact G.ladderAccumulated_zero kappa _
  have hwave : L.HasWaveRungs := by
    intro a
    exact (Lold.stageWeb a).chosenMaximalWave.property
  have hmax : L.HasRoofMaximalRungs := by
    exact canonicalLadderCore_hasRoofMaximalRungs kappa preferred
  have hvalid : HasValidBookkeeping L := by
    exact withValidBookkeeping_hasValidBookkeeping L₀
  exact
    { regular := hkappa
      uncountable := hkappaUncountable
      initialStage := hinitial
      limitStages := by
        change Lold.HasLimitStages
        exact hgeometry.limitStages
      warpStages := by
        change Lold.HasWarpStages
        exact hgeometry.warpStages
      waveRungs := hwave
      roofMaximalRungs := hmax
      exactSuccessorArrows := by
        change Lold.HasExactSuccessorArrows
        exact canonicalLadder_hasExactSuccessorArrows preferred hNoEnter
      freshMarkers := by
        change Lold.HasFreshMarkers
        exact canonicalLadderWithBookkeeping_hasFreshMarkers
          preferred hNoEnter
      markersInjective := by
        change Lold.MarkersInjective
        exact canonicalLadderWithBookkeeping_markersInjective
          preferred hNoEnter
      marksTime := by
        change Lold.MarksTimeAfterExhaustion
        exact canonicalLadderWithBookkeeping_marksTimeAfterExhaustion
          preferred hNoEnter
      accumulatedInitialProvenance := by
        change Lold.HasAccumulatedInitialProvenance
        exact canonicalLadder_hasAccumulatedInitialProvenance
          preferred hNoEnter
      validBookkeeping := hvalid
      hangingProvenance :=
        canonicalDeferredLadder_hasHangingProvenance preferred hNoEnter
      recordedPathsPersist :=
        canonicalDeferredLadder_recordedPathsPersist preferred hNoEnter
      currentInessentialPersists := by
        change Lold.CurrentInessentialPersists
        exact canonicalLadder_currentInessentialPersists preferred hNoEnter
      roofsSourceAtStages := by
        change Lold.RoofsSourceAtStages
        exact hgeometry.roofsSourceAtStages
      frontiersEssential := by
        change Lold.FrontiersAreEssential
        exact Lold.frontiersAreEssential_of_roofsSourceAtStages_assembly
          hgeometry.roofsSourceAtStages
      frontierChronology := by
        change Lold.HasFrontierChronology
        exact hgeometry.frontierChronology
      strictFrontierChronology := by
        change Lold.HasStrictFrontierChronology
        exact canonicalLadder_hasStrictFrontierChronology
          preferred hNoEnter }

theorem canonicalDeferredLadder_isLegal
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular)
    (hkappaUncountable : Cardinal.aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source) :
    IsLegal (canonicalDeferredLadder G kappa preferred) :=
  canonicalDeferredLadder_isDeferredLegal
    preferred hkappa hkappaUncountable hNoEnter

theorem exists_deferredLegalLadder_with_maximalRungs
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular)
    (hkappaUncountable : Cardinal.aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source) :
    ∃ L : G.KappaLadder kappa,
      IsDeferredLegal L ∧ L.HasRoofMaximalRungs := by
  let L := canonicalDeferredLadder G kappa preferred
  have hlegal : IsDeferredLegal L :=
    canonicalDeferredLadder_isDeferredLegal
      preferred hkappa hkappaUncountable hNoEnter
  exact ⟨L, hlegal, hlegal.roofMaximalRungs⟩

end Deferred
end KappaLadder
end DWeb
end Erdos599
