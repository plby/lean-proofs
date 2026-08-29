/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayOldStageIntervalSplice
import ErdosProblems.Erdos599.HalfwaySourceInsideCompatibility
import ErdosProblems.Erdos599.HalfwaySourceWarpDiamondFresh

/-!
# The source diamond for the retained old-stage interval

The row used by Assertion 9.31 is the literal old-frontier--new-frontier
linkage retained by `OldStageIntervalTransaction`.  This file proves
directly that a blueprint roofed by the old frontier is star-compatible
with the inside restriction of that row and forms `A \diamond W[X]`.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.Alternating
open CardinalInduction

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y Z : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

private theorem noIncoming_familyEdges_at_initial
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

namespace OldStageIntervalTransaction

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {z : V}

/-- The retained interval meets the old roof exactly in its old-frontier
initial set. -/
theorem ambientInterval_vertexSet_inter_oldRoof
    (T : OldStageIntervalTransaction C z) :
    Gamma.vertexSet T.ambientInterval ∩ Gamma.roof C.oldSlice =
      C.oldSlice := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨q, hq, hxq⟩, hxRoof⟩
    rw [T.ambientInterval_eq_lift] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    have hxeq : x = r.initial := by
      by_contra hxne
      have hxRawRoof : x ∈ Gamma.roof
          (Gamma.terminalFrontier (C.ladder.warpAt C.oldStage)) := by
        rw [← Gamma.roof_essential,
          ← C.ladder.frontier_eq_essential_terminalFrontier
            C.legal.roofsSourceAtStages C.oldStage]
        exact hxRoof
      exact (C.ladder.liftStagePath_not_mem_roof_of_ne_initial
        C.oldStage r hxq hxne) hxRawRoof
    rw [hxeq, ← T.stageInterval_linkage.initialSet_eq]
    exact ⟨r, hr, rfl⟩
  · intro x hx
    have hxInitial : x ∈
        (C.ladder.stageWeb C.oldStage).initialSet T.stageInterval :=
      T.stageInterval_linkage.initialSet_eq.symm ▸ hx
    obtain ⟨p, hp, hpInitial⟩ := hxInitial
    refine ⟨?_, Gamma.subset_roof C.oldSlice hx⟩
    refine ⟨C.ladder.liftStagePath C.oldStage p, ?_, ?_⟩
    · rw [T.ambientInterval_eq_lift,
        CardinalInduction.SliceSegmentCore.mem_liftStageFamily]
      exact ⟨p, hp, rfl⟩
    · rw [C.ladder.support_liftStagePath, ← hpInitial]
      exact p.initial_mem_support

/-- The actual inside restriction `W[X]` of the retained interval is
compatible with an old-frontier blueprint. -/
theorem SourceInsideRestriction.starCompatible_of_oldStageInterval
    (T : OldStageIntervalTransaction C z)
    (old : LinkageBlueprint Gamma Z kappa) {X : Set V}
    (hOldRoof : old.vertexSet ⊆ Gamma.roof C.oldSlice)
    (hOldTerminal : old.terminalSet = C.oldSlice)
    (I : SourceInsideRestriction (Y := Z) (kappa := kappa)
      T.ambientInterval X) :
    (imaginaryWeb Gamma Z kappa).StarCompatible
      old.paths I.family.paths := by
  intro p hpOld q hqInside x hxp hxq
  have hxOldRoof : x ∈ Gamma.roof C.oldSlice :=
    hOldRoof ⟨p, hpOld, hxp⟩
  have hxInside : x ∈ I.family.vertexSet := ⟨q, hqInside, hxq⟩
  have hxRow : x ∈ Gamma.vertexSet T.ambientInterval :=
    I.vertices_subset_row hxInside
  have hxOldSlice : x ∈ C.oldSlice := by
    rw [← T.ambientInterval_vertexSet_inter_oldRoof]
    exact ⟨hxRow, hxOldRoof⟩
  have hxOldTerminal : x ∈ old.terminalSet :=
    hOldTerminal.symm ▸ hxOldSlice
  have hpTerminal :
      (imaginaryWeb Gamma Z kappa).terminal? p = some x :=
    DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
      (imaginaryWeb Gamma Z kappa) old.isWarp hpOld hxp hxOldTerminal
  refine ⟨hpTerminal, ?_⟩
  have hxRowInitial : x ∈ Gamma.initialSet T.ambientInterval := by
    rw [T.ambientInterval_linkage.initialSet_eq]
    exact hxOldSlice
  have hnoRow : ¬ ∃ y, (y, x) ∈ familyEdges T.ambientInterval :=
    noIncoming_familyEdges_at_initial
      T.ambientInterval_linkage.isWarp hxRowInitial
  have hxInsideInitial : x ∈ I.family.initialSet := by
    rw [SourceFrontAbsorption.initialSet_eq_no_incoming]
    refine ⟨hxInside, ?_⟩
    rintro ⟨y, hyx⟩
    exact hnoRow ⟨y, I.edges_subset_row hyx⟩
  obtain ⟨r, hrInside, hrInitial⟩ := hxInsideInitial
  have hqr : q = r := I.family.path_eq_of_mem_support
    hqInside hrInside hxq (hrInitial.symm ▸ r.initial_mem_support)
  exact (congrArg Path.initial hqr).trans hrInitial

/-- The literal source object `old \diamond W[X]`. -/
def SourceInsideRestriction.oldStageIntervalDiamond
    (T : OldStageIntervalTransaction C z)
    (old : LinkageBlueprint Gamma Z kappa) {X : Set V}
    (hOldRoof : old.vertexSet ⊆ Gamma.roof C.oldSlice)
    (hOldTerminal : old.terminalSet = C.oldSlice)
    (I : SourceInsideRestriction (Y := Z) (kappa := kappa)
      T.ambientInterval X) : LinkageBlueprint Gamma Z kappa :=
  sourceWarpDiamond old I.family
    (SourceInsideRestriction.starCompatible_of_oldStageInterval
      T old hOldRoof hOldTerminal I)

variable (T : OldStageIntervalTransaction C z)
    (old : LinkageBlueprint Gamma Z kappa) {X : Set V}
    (hOldRoof : old.vertexSet ⊆ Gamma.roof C.oldSlice)
    (hOldTerminal : old.terminalSet = C.oldSlice)
    (I : SourceInsideRestriction (Y := Z) (kappa := kappa)
      T.ambientInterval X)

/-- The retained-row diamond introduces no new edge into the old carrier. -/
theorem SourceInsideRestriction.oldStageIntervalDiamond_noNewIncomingOld :
    old.NoNewPredecessorsTo
      (SourceInsideRestriction.oldStageIntervalDiamond
        T old hOldRoof hOldTerminal I) := by
  intro x y hx hyx
  exact sourceWarpDiamond_noNewIncomingOld old I.family I.finiteCharacter
    (SourceInsideRestriction.starCompatible_of_oldStageInterval
      T old hOldRoof hOldTerminal I)
      hx hyx

/-- Set-difference freshness form consumed by the occurrence compiler. -/
theorem SourceInsideRestriction.oldStageIntervalDiamond_fresh_noIncomingOld :
    ∀ {x y : V}, x ∈ old.vertexSet →
      (y, x) ∈
        (SourceInsideRestriction.oldStageIntervalDiamond
          T old hOldRoof hOldTerminal I).edgeSet \
          old.edgeSet → False := by
  intro x y hx hyx
  exact hyx.2
    (SourceInsideRestriction.oldStageIntervalDiamond_noNewIncomingOld
      T old hOldRoof hOldTerminal I hx hyx.1)

/-- If the joint closure contains the scheduled interval front, its whole
carrier is present in the concrete source diamond. -/
theorem SourceInsideRestriction.front_support_subset_oldStageIntervalDiamond
    (hfrontX : T.front.support ⊆ X) :
    T.front.support ⊆
      (SourceInsideRestriction.oldStageIntervalDiamond
        T old hOldRoof hOldTerminal I).vertexSet := by
  intro x hx
  rw [SourceInsideRestriction.oldStageIntervalDiamond,
    vertexSet_sourceWarpDiamond]
  apply Set.mem_union_right
  rw [I.family_vertexSet]
  exact ⟨⟨Sum.inl T.front, T.front_mem_interval, hx⟩, hfrontX hx⟩

/-- Every directed edge of the scheduled front is present in the source
diamond relation. -/
theorem SourceInsideRestriction.front_edgeSet_subset_oldStageIntervalDiamond
    (hfrontX : T.front.support ⊆ X) :
    T.front.edgeSet ⊆
      (SourceInsideRestriction.oldStageIntervalDiamond
        T old hOldRoof hOldTerminal I).edgeSet := by
  intro e he
  rw [SourceInsideRestriction.oldStageIntervalDiamond,
    edgeSet_sourceWarpDiamond old I.family I.finiteCharacter]
  apply Set.mem_union_right
  rw [I.family_edgeSet]
  refine ⟨?_, ?_⟩
  · simp only [familyEdges, Set.mem_iUnion]
    exact ⟨Sum.inl T.front, T.front_mem_interval, he⟩
  · have hend := T.front.edgeSet_subset_support_prod he
    exact ⟨hfrontX hend.1, hfrontX hend.2⟩

end OldStageIntervalTransaction

#print axioms OldStageIntervalTransaction.ambientInterval_vertexSet_inter_oldRoof
#print axioms OldStageIntervalTransaction.SourceInsideRestriction.starCompatible_of_oldStageInterval
#print axioms OldStageIntervalTransaction.SourceInsideRestriction.oldStageIntervalDiamond
#print axioms OldStageIntervalTransaction.SourceInsideRestriction.oldStageIntervalDiamond_noNewIncomingOld
#print axioms OldStageIntervalTransaction.SourceInsideRestriction.front_edgeSet_subset_oldStageIntervalDiamond

end Erdos599.Blueprint.LinkageBlueprint
