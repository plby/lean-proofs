/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating
import ErdosProblems.Erdos599.DeferredSuccessorRoofTransport
import ErdosProblems.Erdos599.RegularSliceComponentReplacement

/-!
# Annularity of ordinary survivor intervals in the deferred ladder

A canonical ladder never introduces a new vertex into an earlier strict
frontier roof.  Consequently a later survivor component can meet that strict
roof only on its earlier prefix.  The interval remaining after that prefix
therefore lies in the annulus between the two displayed frontiers.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularSliceDeferredOrdinaryAnnulus

open DirectedPath

universe u

variable {V : Type u}

/-- A stage-interval realization is annular whenever the ladder has the
canonical no-reentry property between the two stages. -/
theorem stageIntervalRealization_vertexSet_subset_annulus_of_noReentry
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V}
    (hroof : L.RoofsSourceAtStages)
    (hwarp : L.HasWarpStages)
    (hself : ∀ a : Ladder.ExtendedStage kappa,
      Gamma.vertexSet (L.accumulated a) ⊆
        Gamma.roof (Gamma.terminalFrontier (L.accumulated a)))
    (hgrows : Gamma.LadderGrows (L.warpAt delta) (L.warpAt beta))
    (hnoReentry :
      Gamma.vertexSet (L.warpAt beta) ∩
          Gamma.strictRoof
            (Gamma.terminalFrontier (L.warpAt delta)) ⊆
        Gamma.vertexSet (L.warpAt delta))
    (R : SliceCandidate.StageIntervalRealization L delta beta S) :
    Gamma.vertexSet
        (SliceSegmentCore.segmentFamily R.toSegmentRealization) ⊆
      L.lowerRegion delta ∩ L.upperRegion beta := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := hx
  obtain ⟨s, rfl⟩ := SliceSegmentCore.mem_segmentFamily.mp hp
  let segment := R.toSegmentRealization.segment s
  let left := R.leftPrefix s
  let right := R.rightPrefix s
  have hxSegment : x ∈ segment.support := hxp
  have hxRight : x ∈ right.support := by
    let hstart : DirectedPath.Path.initial
        (.inl (R.toSegmentRealization.segment s) : Gamma.DPath) =
          (R.leftPrefix s).finish := by
      change (R.toSegmentRealization.segment s).start =
        (R.leftPrefix s).finish
      exact (R.toSegmentRealization.segment_start s).trans
        (R.left_finish s).symm
    let hinter : (R.leftPrefix s).support ∩
        (R.toSegmentRealization.segment s).support ⊆
          {(R.leftPrefix s).finish} := (R.prefix_inter s).subset
    have happend : DirectedPath.Path.appendFinite (R.leftPrefix s)
        (.inl (R.toSegmentRealization.segment s)) hstart hinter =
          (.inl (R.rightPrefix s) : Gamma.DPath) := by
      convert R.append_eq s
    have hsupport := DirectedPath.Path.support_appendFinite
      (R.leftPrefix s) (.inl (R.toSegmentRealization.segment s))
        hstart hinter
    rw [happend] at hsupport
    change x ∈ DirectedPath.Path.support
      (Sum.inl (R.rightPrefix s) : Gamma.DPath)
    rw [hsupport]
    exact Or.inr hxSegment
  have hrightBeta : (Sum.inl right : Gamma.DPath) ∈
      Gamma.essentialWarpPart (L.warpAt beta) := R.right_mem s
  have hxUpper : x ∈ L.upperRegion beta := by
    have hxVertex : x ∈ Gamma.vertexSet (L.warpAt beta) :=
      ⟨Sum.inl right, hrightBeta.1, hxRight⟩
    have hxRoof := hself (Ladder.Stage.toExtended beta) hxVertex
    change x ∈ Gamma.roof (L.frontier beta)
    rw [L.frontier_eq_essential_terminalFrontier hroof beta,
      Gamma.roof_essential]
    exact hxRoof
  refine ⟨?_, hxUpper⟩
  intro hxStrict
  have hxStrictRaw : x ∈ Gamma.strictRoof
      (Gamma.terminalFrontier (L.warpAt delta)) := by
    simpa only [DWeb.KappaLadder.lowerRegion,
      L.frontier_eq_essential_terminalFrontier hroof delta,
      Gamma.strictRoof_essential] using hxStrict
  have hxOldVertex : x ∈ Gamma.vertexSet (L.warpAt delta) :=
    hnoReentry ⟨⟨Sum.inl right, hrightBeta.1, hxRight⟩, hxStrictRaw⟩
  obtain ⟨q, hqDelta, hxq⟩ := hxOldVertex
  obtain ⟨qLater, hqLater, hqExtends⟩ := hgrows q hqDelta
  have hqLaterEq : qLater = (Sum.inl right : Gamma.DPath) := by
    apply Alternating.DWeb.IsWarp.eq_of_mem_support
      (hwarp (Ladder.Stage.toExtended beta)) hqLater hrightBeta.1
    · exact Gamma.support_mono_of_extends hqExtends hxq
    · exact hxRight
  have hrightInitial : right.start = left.start := by
    have h := DirectedPath.Path.initial_appendFinite
      (R.leftPrefix s) (.inl (R.toSegmentRealization.segment s))
      (R.toSegmentRealization.segment_start s |>.trans
        (R.left_finish s).symm)
      (R.prefix_inter s).subset
    rw [R.append_eq s] at h
    exact h
  have hqInitial : q.initial =
      DirectedPath.Path.initial (Sum.inl left : Gamma.DPath) := by
    calc
      q.initial = qLater.initial := Gamma.extends_initial hqExtends
      _ = DirectedPath.Path.initial (Sum.inl right : Gamma.DPath) :=
        congrArg DirectedPath.Path.initial hqLaterEq
      _ = DirectedPath.Path.initial (Sum.inl left : Gamma.DPath) :=
        hrightInitial
  have hqEq : q = (Sum.inl left : Gamma.DPath) :=
    DWeb.IsWarp.eq_of_initial_eq Gamma
      (hwarp (Ladder.Stage.toExtended delta)) hqDelta
      (R.left_mem s).1 hqInitial
  have hxLeft : x ∈ left.support := by
    simpa only [hqEq, DirectedPath.Path.support] using hxq
  have hxFinish : x = left.finish := by
    apply Set.mem_singleton_iff.mp
    rw [← R.prefix_inter s]
    exact ⟨hxLeft, hxSegment⟩
  have hleftEssential : left.finish ∈
      Gamma.essential (Gamma.terminalFrontier (L.warpAt delta)) := by
    obtain ⟨t, ht, htEssential⟩ := (R.left_mem s).2
    have hfinish : left.finish = t := Option.some.inj ht
    exact hfinish ▸ htEssential
  exact hxStrictRaw.2 (hxFinish ▸ hleftEssential)

/-- Canonical-deferred specialization of the no-reentry annulus theorem. -/
theorem canonicalDeferred_stageIntervalRealization_vertexSet_subset_annulus
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hroof : (DWeb.KappaLadder.Deferred.canonicalDeferredLadder
      Gamma kappa preferred).RoofsSourceAtStages)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta < beta)
    (hgrows : Gamma.LadderGrows
      ((DWeb.KappaLadder.Deferred.canonicalDeferredLadder
        Gamma kappa preferred).warpAt delta)
      ((DWeb.KappaLadder.Deferred.canonicalDeferredLadder
        Gamma kappa preferred).warpAt beta))
    {S : Set V}
    (R : SliceCandidate.StageIntervalRealization
      (DWeb.KappaLadder.Deferred.canonicalDeferredLadder
        Gamma kappa preferred) delta beta S) :
    Gamma.vertexSet
        (SliceSegmentCore.segmentFamily R.toSegmentRealization) ⊆
      (DWeb.KappaLadder.Deferred.canonicalDeferredLadder
        Gamma kappa preferred).lowerRegion delta ∩
      (DWeb.KappaLadder.Deferred.canonicalDeferredLadder
        Gamma kappa preferred).upperRegion beta := by
  let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder
    Gamma kappa preferred
  apply stageIntervalRealization_vertexSet_subset_annulus_of_noReentry
    hroof
  · intro a
    change Gamma.IsWarp
      (Gamma.canonicalLadderAccumulated kappa preferred a)
    exact (DWeb.KappaLadder.canonicalLadder_geometry
      (G := Gamma) preferred hNoEnter).warpStages a
  · exact (DWeb.KappaLadder.canonicalLadder_geometry
      (G := Gamma) preferred hNoEnter).selfRoofing
  · exact hgrows
  · change Gamma.vertexSet
        (Gamma.canonicalLadderAccumulated kappa preferred
          (Ladder.Stage.toExtended beta)) ∩
      Gamma.strictRoof
        (Gamma.terminalFrontier
          (Gamma.canonicalLadderAccumulated kappa preferred
            (Ladder.Stage.toExtended delta))) ⊆
      Gamma.vertexSet
        (Gamma.canonicalLadderAccumulated kappa preferred
          (Ladder.Stage.toExtended delta))
    exact DWeb.KappaLadder.canonicalAccumulated_no_strictRoof_reentry
      preferred hNoEnter hdeltaBeta.le

/-- The literal ordinary-annularity premise of deferred component
replacement, discharged for the canonical deferred ladder.  The exceptional
closure and its survivor proof affect which interval realization is selected;
no additional geometry is needed once canonical no-reentry is available. -/
theorem canonicalDeferred_ordinaryAnnular
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hroof : (DWeb.KappaLadder.Deferred.canonicalDeferredLadder
      Gamma kappa preferred).RoofsSourceAtStages)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta < beta)
    (hgrows : Gamma.LadderGrows
      ((DWeb.KappaLadder.Deferred.canonicalDeferredLadder
        Gamma kappa preferred).warpAt delta)
      ((DWeb.KappaLadder.Deferred.canonicalDeferredLadder
        Gamma kappa preferred).warpAt beta))
    {T : Set Gamma.DPath} :
    ∀ (K : Set Gamma.DPath), K ⊆ T → #K < kappa →
      let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder
        Gamma kappa preferred
      let D := RegularSliceComponentReplacement.exceptionalClosure
        Gamma L delta beta T K
      let S := L.frontier delta \ D
      let R :=
        RegularSliceSurvivors.stageIntervalRealizationOfSubset_of_geometry
          (L := L) (delta := delta) (beta := beta) (S := S)
          (by
            intro x hx
            by_contra hxNot
            apply hx.2
            exact Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2
              ⟨Or.inr ⟨hx.1, hxNot⟩,
                AlternatingComponents.mem_component_self T
                  (Gamma.essentialWarpPart (L.warpAt beta)) x⟩⟩)
          hroof
          (DWeb.KappaLadder.canonicalLadder_geometry
            (G := Gamma) preferred hNoEnter).warpStages
          hgrows
      Gamma.vertexSet
          (SliceSegmentCore.segmentFamily R.toSegmentRealization) ⊆
        L.lowerRegion delta ∩ L.upperRegion beta := by
  intro K _hKT _hKsmall
  dsimp only
  exact canonicalDeferred_stageIntervalRealization_vertexSet_subset_annulus
    preferred hNoEnter hroof hdeltaBeta hgrows _

end RegularSliceDeferredOrdinaryAnnulus
end CardinalInduction
end Erdos599
