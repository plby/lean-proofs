/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredHindranceGrounding
import ErdosProblems.Erdos599.LadderLemma76
import ErdosProblems.Erdos599.LadderSplitProvenance
import ErdosProblems.Erdos599.RegularCardinal

/-!
# The one-sided ladder geometry used by the half-way construction

Only selected markers must lie outside the current roof and occur as
singleton successor paths. This interface makes no assertion about stages
with no selected marker. Historical deferred legality implies it, but a
different marker protocol must supply its fields independently.
-/

namespace Erdos599.DWeb.KappaLadder.Deferred

open Set Cardinal Ladder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

structure HalfwayGeometry (L : G.KappaLadder kappa) : Prop where
  regular : kappa.IsRegular
  uncountable : aleph0 < kappa
  initialStage : L.HasInitialStage
  limitStages : L.HasLimitStages
  warpStages : L.HasWarpStages
  waveRungs : L.HasWaveRungs
  roofMaximalRungs : L.HasRoofMaximalRungs
  exactSuccessorArrows : L.HasExactSuccessorArrows
  markerOutsideRoof : ∀ (a : Stage kappa) (y : V),
    L.marker a = some y → y ∉ G.roof (L.frontier a)
  markerInserted : ∀ (a : Stage kappa) (y : V),
    L.marker a = some y → G.trivialPath y ∈ L.successorWarp a
  markersInjective : L.MarkersInjective
  accumulatedInitialProvenance : L.HasAccumulatedInitialProvenance
  validBookkeeping : HasValidBookkeeping L
  hangingProvenance : L.HasHangingProvenance
  recordedPathsPersist : L.RecordedPathsPersist
  currentInessentialPersists : L.CurrentInessentialPersists
  roofsSourceAtStages : L.RoofsSourceAtStages
  frontiersEssential : L.FrontiersAreEssential
  frontierChronology : L.HasFrontierChronology
  strictFrontierChronology : L.HasStrictFrontierChronology

theorem IsDeferredLegal.halfwayGeometry {L : G.KappaLadder kappa}
    (hL : IsDeferredLegal L) : HalfwayGeometry L where
  regular := hL.regular
  uncountable := hL.uncountable
  initialStage := hL.initialStage
  limitStages := hL.limitStages
  warpStages := hL.warpStages
  waveRungs := hL.waveRungs
  roofMaximalRungs := hL.roofMaximalRungs
  exactSuccessorArrows := hL.exactSuccessorArrows
  markerOutsideRoof := by
    intro a y hy hyRoof
    have hyCandidate : y ∈ L.markerCandidates a := (hL.freshMarkers.2 a y hy).1
    have hyNotFrontier : y ∉ L.frontier a := fun hf ↦ hyCandidate.2 (Or.inl hf)
    have hyNotEssential : y ∉ G.essential (L.frontier a) := by
      rw [hL.frontiersEssential a]
      exact hyNotFrontier
    have hyStrict : y ∈ G.strictRoof (L.frontier a) := ⟨hyRoof, hyNotEssential⟩
    apply hyCandidate.1.2
    rw [L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages a,
      G.strictRoof_essential] at hyStrict
    exact hyStrict
  markerInserted := fun a y hy ↦ (hL.freshMarkers.2 a y hy).2
  markersInjective := hL.markersInjective
  accumulatedInitialProvenance := hL.accumulatedInitialProvenance
  validBookkeeping := hL.validBookkeeping
  hangingProvenance := hL.hangingProvenance
  recordedPathsPersist := hL.recordedPathsPersist
  currentInessentialPersists := hL.currentInessentialPersists
  roofsSourceAtStages := hL.roofsSourceAtStages
  frontiersEssential := hL.frontiersEssential
  frontierChronology := hL.frontierChronology
  strictFrontierChronology := hL.strictFrontierChronology

instance IsDeferredLegal.instCoeHalfwayGeometry {L : G.KappaLadder kappa} :
    CoeOut (IsDeferredLegal L) (HalfwayGeometry L) where
  coe := IsDeferredLegal.halfwayGeometry

theorem HalfwayGeometry.lemma76Data {L : G.KappaLadder kappa}
    (hL : HalfwayGeometry L) : L.Lemma76Data :=
  ⟨hL.waveRungs, hL.exactSuccessorArrows, hL.roofsSourceAtStages, hL.recordedPathsPersist⟩

/-- A selected marker starts an actual limiting component. Only singleton
insertion and the genuine threadwise-limit law enter this argument. -/
theorem HalfwayGeometry.exists_limitPath_initial_of_marker
    {L : G.KappaLadder kappa} (hL : HalfwayGeometry L)
    {a : Stage kappa} {y : V} (hy : L.marker a = some y) :
    ∃ p ∈ L.limitWarp, p.initial = y := by
  have hlimit : Order.IsSuccLimit kappa.ord := Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  let b : Stage kappa := ⟨a.1 + 1, hlimit.succ_lt a.2⟩
  have hyStage : G.trivialPath y ∈ L.warpAt b := hL.markerInserted a y hy
  obtain ⟨p, hp, hyp⟩ := hL.limitStages.grows_to_limit
    (finalStage kappa) hlimit ⟨b.1, b.2⟩ (G.trivialPath y) hyStage
  refine ⟨p, hp, ?_⟩
  simpa only [G.initial_trivialPath] using (G.extends_initial hyp).symm

#print axioms IsDeferredLegal.halfwayGeometry
#print axioms HalfwayGeometry.lemma76Data
#print axioms HalfwayGeometry.exists_limitPath_initial_of_marker

end Erdos599.DWeb.KappaLadder.Deferred
