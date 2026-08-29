/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingDescentBridge
import ErdosProblems.Erdos599.LadderHangingProvenance
import ErdosProblems.Erdos599.LadderPersistence
import ErdosProblems.Erdos599.LadderSuccessorBridge

/-!
# Split provenance for successor-normalized ladder records

The successor-normalized bookkeeping may record a path which was not yet
inessential in the current warp.  Consequently the strict provenance field
`KappaLadder.HasHangingProvenance` is too strong for the canonical recursion:
a genuinely new record may start at the marker inserted at the same stage.

This file records the sound replacement.  A hanging record either starts at
a strictly earlier marker, or it is genuinely new at the successor and starts
at the current marker.  For records which were already current, the second
case is impossible, recovering the strict provenance used by the regressive
argument on that part of the obstruction set.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- Sound provenance for successor-normalized hanging records.  The second
alternative names the only same-stage case and records that it is genuinely
new, rather than merely omitting the strict inequality. -/
structure HasSplitHangingProvenance (L : G.KappaLadder kappa) : Prop where
  resolve : ∀ (a : Ladder.Stage kappa), a ∈ L.phiHanging →
    ∀ (p : G.DPath), L.chosen a = some p →
      (∃ b : Ladder.Stage kappa,
          b < a ∧ L.marker b = some p.initial) ∨
        (p ∉ G.inessentialPaths (L.warpAt a) ∧
          L.marker a = some p.initial)

/-- The legacy strict provenance law implies split provenance, with the
same-stage branch unused. -/
theorem HasHangingProvenance.hasSplitHangingProvenance
    {L : G.KappaLadder kappa} (hL : L.HasHangingProvenance) :
    L.HasSplitHangingProvenance := by
  constructor
  intro a ha p hp
  exact Or.inl (hL a ha p hp)

/-- On a record already inessential in the current warp, split provenance
specializes to strict earlier-marker provenance. -/
theorem HasSplitHangingProvenance.prior
    {L : G.KappaLadder kappa} (hL : L.HasSplitHangingProvenance)
    {a : Ladder.Stage kappa} (ha : a ∈ L.phiHanging)
    {p : G.DPath} (hp : L.chosen a = some p)
    (hpCurrent : p ∈ G.inessentialPaths (L.warpAt a)) :
    ∃ b : Ladder.Stage kappa,
      b < a ∧ L.marker b = some p.initial := by
  rcases hL.resolve a ha p hp with hprior | ⟨hpNotCurrent, _⟩
  · exact hprior
  · exact (hpNotCurrent hpCurrent).elim

/-- On a genuinely successor-new record, split provenance exposes the exact
remaining dichotomy: an earlier marker or the marker born at this stage. -/
theorem HasSplitHangingProvenance.fresh
    {L : G.KappaLadder kappa} (hL : L.HasSplitHangingProvenance)
    {a : Ladder.Stage kappa} (ha : a ∈ L.phiHanging)
    {p : G.DPath} (hp : L.chosen a = some p)
    (_hpFresh : p ∉ G.inessentialPaths (L.warpAt a)) :
    (∃ b : Ladder.Stage kappa,
        b < a ∧ L.marker b = some p.initial) ∨
      L.marker a = some p.initial := by
  rcases hL.resolve a ha p hp with hprior | hsame
  · exact Or.inl hprior
  · exact Or.inr hsame.2

/-- Accumulated provenance yields split provenance as soon as every current
marker is outside the current accumulated family.  This is the exact local
geometry supplied by the canonical recursion. -/
theorem hasSplitHangingProvenance_of_accumulatedInitialProvenance
    {L : G.KappaLadder kappa}
    (hprovenance : L.HasAccumulatedInitialProvenance)
    (hvalid : L.HasValidBookkeeping)
    (hmarkerOutside : ∀ (a : Ladder.Stage kappa) (y : V),
      L.marker a = some y → y ∉ G.vertexSet (L.warpAt a)) :
    L.HasSplitHangingProvenance := by
  constructor
  intro a ha p hp
  have hpNext : p ∈ G.inessentialPaths (L.successorWarp a) :=
    (L.bookkeeping.chosen_mem_available hvalid hp).1
  rcases hprovenance (Ladder.Stage.succExtended a) p hpNext.1 with
      hpSource | ⟨b, hba, hb⟩
  · exact (ha.2 ⟨p, hp, hpSource⟩).elim
  · have hble : b.1 ≤ a.1 := by
      change b.1 + 1 ≤ a.1 + 1 at hba
      rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one] at hba
      exact Order.succ_le_succ_iff.mp hba
    rcases hble.lt_or_eq with hblt | hbeq
    · exact Or.inl ⟨b, hblt, hb⟩
    · right
      have hmarker : L.marker a = some p.initial := by
        simpa [Subtype.ext hbeq] using hb
      refine ⟨?_, hmarker⟩
      intro hpCurrent
      exact hmarkerOutside a p.initial hmarker
        ⟨p, hpCurrent.1, p.initial_mem_support⟩

/-- The marker chosen by the canonical recursion is outside the accumulated
family at the stage where it is chosen. -/
theorem canonicalLadder_marker_not_mem_currentVertexSet
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : Ladder.Stage kappa) (y : V)
    (hy : (canonicalLadder G kappa preferred).marker a = some y) :
    y ∉ G.vertexSet ((canonicalLadder G kappa preferred).warpAt a) := by
  let L := canonicalLadder G kappa preferred
  let s := G.canonicalLadderState kappa preferred
    (Ladder.Stage.toExtended a)
  have hgeometry : CanonicalLadderGeometry L :=
    canonicalLadder_geometry preferred hNoEnter
  have hcontact : G.LadderStateContactsStageSource s :=
    G.ladderStateContactsStageSource_of_roofs s
      (hgeometry.roofsSourceAtStages (Ladder.Stage.toExtended a))
      (hgeometry.selfRoofing (Ladder.Stage.toExtended a))
  change G.ladderMarkerOfState (preferred a) s = some y at hy
  change y ∉ G.vertexSet s.1
  exact G.ladderMarkerOfState_not_mem_old_vertexSet hcontact hy

/-- The canonical successor-normalized bookkeeping satisfies the sound
split provenance law. -/
theorem canonicalLadder_hasSplitHangingProvenance
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (canonicalLadder G kappa preferred).HasSplitHangingProvenance := by
  let L₀ := G.canonicalLadderCore kappa preferred
  apply hasSplitHangingProvenance_of_accumulatedInitialProvenance
    (canonicalLadder_hasAccumulatedInitialProvenance preferred hNoEnter)
    L₀.withValidBookkeeping_hasValidBookkeeping
  intro a y hy
  exact canonicalLadder_marker_not_mem_currentVertexSet
    preferred hNoEnter a y hy

/-- The part of ladder legality needed by the provenance/stationarity
argument, with the false all-record strictness field replaced by split
provenance.  Other geometric legality fields are intentionally not repeated
here; this is the smallest sound interface for the affected argument. -/
structure SplitLegalityInvariant (L : G.KappaLadder kappa) : Prop where
  regular : kappa.IsRegular
  uncountable : ℵ₀ < kappa
  warpStages : L.HasWarpStages
  validBookkeeping : L.HasValidBookkeeping
  recordedPathsPersist : L.RecordedPathsPersist
  splitHangingProvenance : L.HasSplitHangingProvenance

/-- The complete, sound legality package for the successor-normalized
canonical ladder.  This differs from the legacy `KappaLadder.IsLegal` in
exactly one field: hanging records carry the proved earlier-or-current
split provenance instead of the false assertion that every record has a
strictly earlier origin.  All geometric and bookkeeping laws are unchanged,
so consumers which do not use hanging provenance can migrate by projecting
the same named fields from this structure. -/
structure IsSplitLegal (L : G.KappaLadder kappa) : Prop where
  regular : kappa.IsRegular
  uncountable : ℵ₀ < kappa
  initialStage : L.HasInitialStage
  limitStages : L.HasLimitStages
  warpStages : L.HasWarpStages
  waveRungs : L.HasWaveRungs
  roofMaximalRungs : L.HasRoofMaximalRungs
  exactSuccessorArrows : L.HasExactSuccessorArrows
  freshMarkers : L.HasFreshMarkers
  markersInjective : L.MarkersInjective
  marksTime : L.MarksTimeAfterExhaustion
  validBookkeeping : L.HasValidBookkeeping
  splitHangingProvenance : L.HasSplitHangingProvenance
  recordedPathsPersist : L.RecordedPathsPersist
  currentInessentialPersists : L.CurrentInessentialPersists
  roofsSourceAtStages : L.RoofsSourceAtStages
  frontiersEssential : L.FrontiersAreEssential
  frontierChronology : L.HasFrontierChronology
  strictFrontierChronology : L.HasStrictFrontierChronology

/-- Legacy legality embeds into the repaired package. -/
theorem IsLegal.isSplitLegal {L : G.KappaLadder kappa} (hL : L.IsLegal) :
    L.IsSplitLegal where
  regular := hL.regular
  uncountable := hL.uncountable
  initialStage := hL.initialStage
  limitStages := hL.limitStages
  warpStages := hL.warpStages
  waveRungs := hL.waveRungs
  roofMaximalRungs := hL.roofMaximalRungs
  exactSuccessorArrows := hL.exactSuccessorArrows
  freshMarkers := hL.freshMarkers
  markersInjective := hL.markersInjective
  marksTime := hL.marksTime
  validBookkeeping := hL.validBookkeeping
  splitHangingProvenance := hL.hangingProvenance.hasSplitHangingProvenance
  recordedPathsPersist := hL.recordedPathsPersist
  currentInessentialPersists := hL.currentInessentialPersists
  roofsSourceAtStages := hL.roofsSourceAtStages
  frontiersEssential := hL.frontiersEssential
  frontierChronology := hL.frontierChronology
  strictFrontierChronology := hL.strictFrontierChronology

/-- The smaller stationarity interface is a projection of full split
legality. -/
theorem IsSplitLegal.splitLegalityInvariant
    {L : G.KappaLadder kappa} (hL : L.IsSplitLegal) :
    L.SplitLegalityInvariant where
  regular := hL.regular
  uncountable := hL.uncountable
  warpStages := hL.warpStages
  validBookkeeping := hL.validBookkeeping
  recordedPathsPersist := hL.recordedPathsPersist
  splitHangingProvenance := hL.splitHangingProvenance

/-- The canonical recursion satisfies the sound split legality interface. -/
theorem canonicalLadder_splitLegalityInvariant
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : ℵ₀ < kappa)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (canonicalLadder G kappa preferred).SplitLegalityInvariant := by
  let L₀ := G.canonicalLadderCore kappa preferred
  have hgeometry :
      CanonicalLadderGeometry (canonicalLadder G kappa preferred) :=
    canonicalLadder_geometry preferred hNoEnter
  exact
    { regular := hkappa
      uncountable := huncountable
      warpStages := hgeometry.warpStages
      validBookkeeping := L₀.withValidBookkeeping_hasValidBookkeeping
      recordedPathsPersist :=
        canonicalLadder_recordedPathsPersist preferred hNoEnter
      splitHangingProvenance :=
        canonicalLadder_hasSplitHangingProvenance preferred hNoEnter }

/-- The canonical successor-normalized ladder satisfies every sound
construction law, with the split provenance theorem in place of the invalid
all-record strictness claim.  This is the unconditional legality theorem
used by the regular-cardinal branch. -/
theorem canonicalLadder_isSplitLegal
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : ℵ₀ < kappa)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (canonicalLadder G kappa preferred).IsSplitLegal := by
  let L₀ := G.canonicalLadderCore kappa preferred
  let L := canonicalLadder G kappa preferred
  have hgeometry : CanonicalLadderGeometry L :=
    canonicalLadder_geometry preferred hNoEnter
  have hinitial : L.HasInitialStage := by
    change (G.canonicalLadderCore kappa preferred).HasInitialStage
    exact G.ladderAccumulated_zero kappa _
  have hwave : L.HasWaveRungs := by
    intro a
    exact ((G.canonicalLadderCore kappa preferred).stageWeb a)
      |>.chosenMaximalWave.property
  exact
    { regular := hkappa
      uncountable := huncountable
      initialStage := hinitial
      limitStages := hgeometry.limitStages
      warpStages := hgeometry.warpStages
      waveRungs := hwave
      roofMaximalRungs :=
        canonicalLadder_withValidBookkeeping_hasRoofMaximalRungs preferred
      exactSuccessorArrows :=
        canonicalLadder_hasExactSuccessorArrows preferred hNoEnter
      freshMarkers :=
        canonicalLadderWithBookkeeping_hasFreshMarkers preferred hNoEnter
      markersInjective := canonicalLadder_markersInjective preferred hNoEnter
      marksTime :=
        canonicalLadderWithBookkeeping_marksTimeAfterExhaustion
          preferred hNoEnter
      validBookkeeping := L₀.withValidBookkeeping_hasValidBookkeeping
      splitHangingProvenance :=
        canonicalLadder_hasSplitHangingProvenance preferred hNoEnter
      recordedPathsPersist :=
        canonicalLadder_recordedPathsPersist preferred hNoEnter
      currentInessentialPersists :=
        canonicalLadder_currentInessentialPersists preferred hNoEnter
      roofsSourceAtStages := hgeometry.roofsSourceAtStages
      frontiersEssential :=
        L.frontiersAreEssential_of_roofsSourceAtStages_assembly
          hgeometry.roofsSourceAtStages
      frontierChronology := hgeometry.frontierChronology
      strictFrontierChronology :=
        canonicalLadder_hasStrictFrontierChronology preferred hNoEnter }

/-! ## Bridge to the existing old/new grounding split -/

/-- The existing `priorInessentialRecordStages` branch receives exactly the
strict provenance expected by the legacy regressive argument. -/
theorem HasSplitHangingProvenance.priorInessentialRecord_hasStrictProvenance
    {L : G.KappaLadder kappa} (hL : L.HasSplitHangingProvenance)
    {a : Ladder.Stage kappa} (ha : a ∈ L.phiHanging)
    (haPrior : a ∈ L.priorInessentialRecordStages)
    {p : G.DPath} (hp : L.chosen a = some p) :
    ∃ b : Ladder.Stage kappa,
      b < a ∧ L.marker b = some p.initial := by
  obtain ⟨q, hq, hqCurrent⟩ := haPrior
  have hqp : q = p := Option.some.inj (hq.symm.trans hp)
  subst q
  exact hL.prior ha hp hqCurrent

/-- The existing `freshInessentialRecordStages` branch receives the honest
earlier-or-same-stage marker dichotomy. -/
theorem HasSplitHangingProvenance.freshInessentialRecord_markerDichotomy
    {L : G.KappaLadder kappa} (hL : L.HasSplitHangingProvenance)
    (hvalid : L.HasValidBookkeeping)
    {a : Ladder.Stage kappa} (ha : a ∈ L.phiHanging)
    (haFresh : a ∈ L.freshInessentialRecordStages)
    {p : G.DPath} (hp : L.chosen a = some p) :
    (∃ b : Ladder.Stage kappa,
        b < a ∧ L.marker b = some p.initial) ∨
      L.marker a = some p.initial := by
  obtain ⟨q, hq, _hqNext, hqNotCurrent, _hqNew⟩ :=
    L.freshInessentialRecordStages_spec hvalid haFresh
  have hqp : q = p := Option.some.inj (hq.symm.trans hp)
  subst q
  exact hL.fresh ha hp hqNotCurrent

/-! ## The regressive argument on the sound prior-record branch -/

/-- Hanging records which were already current at their named stage. -/
def priorHangingStages (L : G.KappaLadder kappa) :
    Set (Ladder.Stage kappa) :=
  L.phiHanging ∩ L.priorInessentialRecordStages

/-- The strictly earlier marker supporting a prior hanging record. -/
noncomputable def priorHangingOrigin (L : G.KappaLadder kappa)
    (hL : L.SplitLegalityInvariant) (a : Ladder.Stage kappa) :
    Ladder.Stage kappa := by
  classical
  exact if ha : a ∈ L.priorHangingStages then
    Classical.choose
      (hL.splitHangingProvenance.priorInessentialRecord_hasStrictProvenance
        ha.1 ha.2
        (L.chosen_selectedPath hL.validBookkeeping ⟨a, ha.1.1⟩))
  else a

theorem priorHangingOrigin_spec (L : G.KappaLadder kappa)
    (hL : L.SplitLegalityInvariant) {a : Ladder.Stage kappa}
    (ha : a ∈ L.priorHangingStages) :
    L.priorHangingOrigin hL a < a ∧
      L.marker (L.priorHangingOrigin hL a) =
        some (L.selectedPath hL.validBookkeeping ⟨a, ha.1.1⟩).initial := by
  rw [priorHangingOrigin, dif_pos ha]
  exact Classical.choose_spec
    (hL.splitHangingProvenance.priorInessentialRecord_hasStrictProvenance
      ha.1 ha.2
      (L.chosen_selectedPath hL.validBookkeeping ⟨a, ha.1.1⟩))

theorem priorHangingOrigin_regressive (L : G.KappaLadder kappa)
    (hL : L.SplitLegalityInvariant) :
    Stationary.IsRegressiveOn L.priorHangingStages
      (L.priorHangingOrigin hL) :=
  fun _ ha ↦ (L.priorHangingOrigin_spec hL ha).1

/-- The usual path-persistence proof of injectivity remains valid after
restricting the domain to prior hanging records. -/
theorem priorHangingOrigin_injOn (L : G.KappaLadder kappa)
    (hL : L.SplitLegalityInvariant) :
    Set.InjOn (L.priorHangingOrigin hL) L.priorHangingStages := by
  intro a ha b hb hab
  let pa : G.DPath :=
    L.selectedPath hL.validBookkeeping ⟨a, ha.1.1⟩
  let pb : G.DPath :=
    L.selectedPath hL.validBookkeeping ⟨b, hb.1.1⟩
  have hpa : L.chosen a = some pa :=
    L.chosen_selectedPath hL.validBookkeeping ⟨a, ha.1.1⟩
  have hpb : L.chosen b = some pb :=
    L.chosen_selectedPath hL.validBookkeeping ⟨b, hb.1.1⟩
  have hinitial : pa.initial = pb.initial := by
    have hma := (L.priorHangingOrigin_spec hL ha).2
    have hmb := (L.priorHangingOrigin_spec hL hb).2
    rw [hab] at hma
    exact Option.some.inj (hma.symm.trans hmb)
  rcases lt_trichotomy a b with hablt | rfl | hbalt
  · have hpaIE : pa ∈ G.inessentialPaths (L.successorWarp b) := by
      apply hL.recordedPathsPersist a pa hpa
        (Ladder.Stage.succExtended b)
      change a.1 + 1 ≤ b.1 + 1
      rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
      exact Order.succ_le_succ hablt.le
    have hpaWarp : pa ∈ L.successorWarp b := hpaIE.1
    have hpbWarp : pb ∈ L.successorWarp b :=
      ((L.bookkeeping.chosen_mem_available
        hL.validBookkeeping hpb).1).1
    by_cases hp : pa = pb
    · exact L.bookkeeping.chosen_stage_unique hL.validBookkeeping
        hpa (hp ▸ hpb)
    · exact False.elim <| Set.disjoint_left.1
        (hL.warpStages (Ladder.Stage.succExtended b)
          hpaWarp hpbWarp hp)
        pa.initial_mem_support (hinitial ▸ pb.initial_mem_support)
  · rfl
  · have hpbIE : pb ∈ G.inessentialPaths (L.successorWarp a) := by
      apply hL.recordedPathsPersist b pb hpb
        (Ladder.Stage.succExtended a)
      change b.1 + 1 ≤ a.1 + 1
      rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
      exact Order.succ_le_succ hbalt.le
    have hpbWarp : pb ∈ L.successorWarp a := hpbIE.1
    have hpaWarp : pa ∈ L.successorWarp a :=
      ((L.bookkeeping.chosen_mem_available
        hL.validBookkeeping hpa).1).1
    by_cases hp : pa = pb
    · exact L.bookkeeping.chosen_stage_unique hL.validBookkeeping
        hpa (hp ▸ hpb)
    · exact False.elim <| Set.disjoint_left.1
        (hL.warpStages (Ladder.Stage.succExtended a)
          hpaWarp hpbWarp hp)
        pa.initial_mem_support (hinitial ▸ pb.initial_mem_support)

/-- The sound replacement for `phiHanging_not_stationary_of_legal`: the
prior-record part of the hanging set is nonstationary.  The fresh same-stage
part is deliberately left for the equal-index grounding branch. -/
theorem priorHangingStages_not_stationary (L : G.KappaLadder kappa)
    (hL : L.SplitLegalityInvariant) :
    ¬ Stationary.IsStationaryBelow kappa L.priorHangingStages :=
  Stationary.not_isStationaryBelow_of_injOn_regressive
    hL.uncountable hL.regular
    (L.priorHangingOrigin_regressive hL)
    (L.priorHangingOrigin_injOn hL)

end KappaLadder
end DWeb
end Erdos599
