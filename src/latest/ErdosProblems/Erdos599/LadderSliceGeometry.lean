/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularStageGrowth
import ErdosProblems.Erdos599.LadderRecordCardinal

/-!
# Marker-independent geometry for ordinary slices

This interface retains the exact geometric and ordinary-bookkeeping laws
used by slice construction. It does not assert the historical marker
exhaustion rule or hanging-record provenance. Old split legality supplies
it by a proved one-way coercion; new constructions must prove every field.
-/

namespace Erdos599.DWeb.KappaLadder

open Set Cardinal Ladder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

structure SliceGeometry (L : G.KappaLadder kappa) : Prop where
  regular : kappa.IsRegular
  uncountable : aleph0 < kappa
  initialStage : L.HasInitialStage
  limitStages : L.HasLimitStages
  warpStages : L.HasWarpStages
  waveRungs : L.HasWaveRungs
  roofMaximalRungs : L.HasRoofMaximalRungs
  exactSuccessorArrows : L.HasExactSuccessorArrows
  validBookkeeping : L.HasValidBookkeeping
  recordedPathsPersist : L.RecordedPathsPersist
  currentInessentialPersists : L.CurrentInessentialPersists
  roofsSourceAtStages : L.RoofsSourceAtStages
  frontiersEssential : L.FrontiersAreEssential
  frontierChronology : L.HasFrontierChronology
  strictFrontierChronology : L.HasStrictFrontierChronology
  grows : ∀ {a b : Stage kappa}, a ≤ b → G.LadderGrows (L.warpAt a) (L.warpAt b)

theorem IsSplitLegal.sliceGeometry {L : G.KappaLadder kappa} (hL : L.IsSplitLegal) :
    L.SliceGeometry where
  regular := hL.regular
  uncountable := hL.uncountable
  initialStage := hL.initialStage
  limitStages := hL.limitStages
  warpStages := hL.warpStages
  waveRungs := hL.waveRungs
  roofMaximalRungs := hL.roofMaximalRungs
  exactSuccessorArrows := hL.exactSuccessorArrows
  validBookkeeping := hL.validBookkeeping
  recordedPathsPersist := hL.recordedPathsPersist
  currentInessentialPersists := hL.currentInessentialPersists
  roofsSourceAtStages := hL.roofsSourceAtStages
  frontiersEssential := hL.frontiersEssential
  frontierChronology := hL.frontierChronology
  strictFrontierChronology := hL.strictFrontierChronology
  grows := CardinalInduction.warpAt_grows_of_le hL

instance IsSplitLegal.instCoeSliceGeometry {L : G.KappaLadder kappa} :
    CoeOut L.IsSplitLegal L.SliceGeometry where
  coe := IsSplitLegal.sliceGeometry

theorem SliceGeometry.mk_inessentialSuccessor_lt_of_not_mem_phi
    {L : G.KappaLadder kappa} (_hL : L.SliceGeometry) {a : Stage kappa} (ha : a ∉ L.phi) :
    #(G.inessentialPaths (L.successorWarp a)) < kappa := by
  have hsub : G.inessentialPaths (L.successorWarp a) ⊆ L.bookkeeping.recordedBefore a := by
    intro p hp
    by_contra hnot
    exact ha ⟨p, hp, hnot⟩
  exact (Cardinal.mk_subtype_mono hsub).trans_lt (L.mk_recordedBefore_lt a)

theorem SliceGeometry.mk_inessentialWarpAt_lt_of_not_mem_phi
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry) {a : Stage kappa} (ha : a ∉ L.phi) :
    #(G.inessentialPaths (L.warpAt a)) < kappa :=
  (Cardinal.mk_subtype_mono (hL.currentInessentialPersists a)).trans_lt
    (hL.mk_inessentialSuccessor_lt_of_not_mem_phi ha)

#print axioms IsSplitLegal.sliceGeometry
#print axioms SliceGeometry.mk_inessentialWarpAt_lt_of_not_mem_phi

end Erdos599.DWeb.KappaLadder
