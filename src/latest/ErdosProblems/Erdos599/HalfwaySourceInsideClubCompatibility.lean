/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingSuccessorRoofTransport
import ErdosProblems.Erdos599.HalfwaySourceInsideCompatibility
import ErdosProblems.Erdos599.HalfwayStageGeometryCore
import ErdosProblems.Erdos599.SliceDeltaLift

/-!
# Club-stage compatibility of the literal inside row

Assertion 9.31 forms `A \diamond W[X]`.  This file proves the actual
compatibility needed for that diamond.  A target row lifted from the later
stage meets the old roof exactly in its prescribed initial set `A`; passing
to the literal restriction `W[X]` can delete edges, but cannot create an
incoming edge at one of those row initials.

This focused statement deliberately does not import the legacy aggregate
stage-geometry module and does not turn the whole target row into a retained
reference warp.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y Z : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- A lifted linkage from the later quotient stage meets the later frontier
roof precisely in the linkage's initial set. -/
theorem ClubStageGeometry.vertexSet_liftStageRow_inter_outerRoof
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {A : Set V} {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P) :
    Gamma.vertexSet
        (CardinalInduction.SliceSegmentCore.liftStageFamily
          C.ladder C.newStage P) ∩ C.outerRoof = A := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨q, hq, hxq⟩, hxRoof⟩
    rw [CardinalInduction.SliceSegmentCore.mem_liftStageFamily] at hq
    obtain ⟨r, hrP, rfl⟩ := hq
    have hxeq : x = r.initial := by
      by_contra hxne
      have hxRawRoof : x ∈ Gamma.roof
          (Gamma.terminalFrontier (C.ladder.warpAt C.newStage)) := by
        rw [← Gamma.roof_essential,
          ← C.ladder.frontier_eq_essential_terminalFrontier
            C.legal.roofsSourceAtStages C.newStage]
        exact hxRoof
      exact (C.ladder.liftStagePath_not_mem_roof_of_ne_initial
        C.newStage r hxq hxne) hxRawRoof
    rw [hxeq, ← hP.initialSet_eq]
    exact ⟨r, hrP, rfl⟩
  · intro x hxA
    have hxInitial : x ∈
        (C.ladder.stageWeb C.newStage).initialSet P :=
      hP.initialSet_eq.symm ▸ hxA
    obtain ⟨p, hpP, hpInitial⟩ := hxInitial
    refine ⟨?_, Gamma.subset_roof C.newSlice (hA hxA)⟩
    refine ⟨C.ladder.liftStagePath C.newStage p, ?_, ?_⟩
    · rw [CardinalInduction.SliceSegmentCore.mem_liftStageFamily]
      exact ⟨p, hpP, rfl⟩
    · change x ∈ (C.ladder.liftStagePath C.newStage p).support
      rw [C.ladder.support_liftStagePath, ← hpInitial]
      exact p.initial_mem_support

/-- A warp relation has no incoming edge at one of its initial vertices. -/
private theorem noIncoming_familyEdges_of_mem_initialSet
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W) {x : V}
    (hx : x ∈ Gamma.initialSet W) :
    ¬ ∃ y, (y, x) ∈ familyEdges W := by
  obtain ⟨p, hpW, hpinitial⟩ := hx
  rintro ⟨y, hyx⟩
  simp only [familyEdges, Set.mem_iUnion] at hyx
  obtain ⟨q, hqW, hyxq⟩ := hyx
  have hxp : x ∈ p.support := hpinitial.symm ▸ p.initial_mem_support
  have hxq : x ∈ q.support := (q.edgeSet_subset_support_prod hyxq).2
  have hpq : p = q :=
    DWeb.IsWarp.eq_of_mem_support hW hpW hqW hxp hxq
  subst q
  rcases p with p | r
  · have hpstart : p.start = x := by
      simpa [DirectedPath.Path.initial] using hpinitial
    exact FinitePath.no_incoming_edge_at_start p y (hpstart ▸ hyxq)
  · obtain ⟨n, hn⟩ := hyxq
    have hzero : n + 1 = 0 := by
      apply r.injective
      calc
        r (n + 1) = x := (congrArg Prod.snd hn).symm
        _ = r.initial := hpinitial.symm
        _ = r 0 := rfl
    omega

/-- Concrete club-stage constructor for the compatibility in
`A \diamond W[X]`.  The old blueprint may use a different imaginary
reference `Z` from the club geometry's global reference `Y`. -/
theorem SourceInsideRestriction.starCompatible_of_clubStageRow
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (old : LinkageBlueprint Gamma Z kappa) {A X : Set V}
    (hOldRoof : old.vertexSet ⊆ C.outerRoof)
    (hOldTerminal : old.terminalSet = A)
    {P : Set (C.ladder.stageWeb C.newStage).DPath}
    (hA : A ⊆ C.newSlice)
    (hP : CardinalInduction.IsLinkageBetween
      (C.ladder.stageWeb C.newStage) A
        (C.ladder.stageWeb C.newStage).target P)
    (I : SourceInsideRestriction (Y := Z) (kappa := kappa)
      (CardinalInduction.SliceSegmentCore.liftStageFamily
        C.ladder C.newStage P) X) :
    (imaginaryWeb Gamma Z kappa).StarCompatible old.paths I.family.paths := by
  let W := CardinalInduction.SliceSegmentCore.liftStageFamily
    C.ladder C.newStage P
  have hWwarp : Gamma.IsWarp W :=
    CardinalInduction.SliceSegmentCore.liftStageFamily_isWarp
      C.ladder C.newStage hP.isWarp
  have hWinitial : Gamma.initialSet W = A := by
    dsimp only [W]
    rw [CardinalInduction.SliceSegmentCore.initialSet_liftStageFamily,
      hP.initialSet_eq]
  intro p hpOld q hqInside x hxp hxq
  have hxRoof : x ∈ C.outerRoof := hOldRoof ⟨p, hpOld, hxp⟩
  have hxInside : x ∈ I.family.vertexSet := ⟨q, hqInside, hxq⟩
  have hxRow : x ∈ Gamma.vertexSet W := I.vertices_subset_row hxInside
  have hxA : x ∈ A := by
    rw [← C.vertexSet_liftStageRow_inter_outerRoof hA hP]
    exact ⟨hxRow, hxRoof⟩
  have hxOldTerminal : x ∈ old.terminalSet := hOldTerminal.symm ▸ hxA
  have hpTerminal : (imaginaryWeb Gamma Z kappa).terminal? p = some x :=
    DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
      (imaginaryWeb Gamma Z kappa) old.isWarp hpOld hxp hxOldTerminal
  refine ⟨hpTerminal, ?_⟩
  have hxRowInitial : x ∈ Gamma.initialSet W := hWinitial.symm ▸ hxA
  have hnoRow : ¬ ∃ y, (y, x) ∈ familyEdges W :=
    noIncoming_familyEdges_of_mem_initialSet hWwarp hxRowInitial
  have hxInsideInitial : x ∈ I.family.initialSet := by
    rw [SourceFrontAbsorption.initialSet_eq_no_incoming]
    refine ⟨hxInside, ?_⟩
    rintro ⟨y, hyx⟩
    exact hnoRow ⟨y, I.edges_subset_row hyx⟩
  obtain ⟨r, hrInside, hrinitial⟩ := hxInsideInitial
  have hqr : q = r := I.family.path_eq_of_mem_support
    hqInside hrInside hxq (hrinitial.symm ▸ r.initial_mem_support)
  exact (congrArg Path.initial hqr).trans hrinitial

#print axioms ClubStageGeometry.vertexSet_liftStageRow_inter_outerRoof
#print axioms SourceInsideRestriction.starCompatible_of_clubStageRow

end Erdos599.Blueprint.LinkageBlueprint
