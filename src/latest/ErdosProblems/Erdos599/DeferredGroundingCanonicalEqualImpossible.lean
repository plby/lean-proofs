/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingAuxiliary
import ErdosProblems.Erdos599.DeferredLadderRoofTransport
import ErdosProblems.Erdos599.SplitGroundingFreshMarkerMaximal

/-!
# Equal target routes are impossible for the canonical deferred ladder

Deferred bookkeeping omits the component starting at the marker born at the
current stage.  Hence every chosen component belongs to the pre-marker arrow.
If it is finite, either its terminal is already in the strict pre-marker roof,
or it is essential in that arrow and rung maximality prevents the marker from
making it inessential.  A chosen ray is wholly in the strict pre-marker roof.
Target-pure transport therefore rules out an equal-index route to the retained
marker born at the same stage.

Only the bookkeeping provenance is deferred; all geometric objects are
definitionally those of `canonicalLadderCore`.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath Ladder

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

private theorem deferredTargetMarker_mem_splitTargetMarkers
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source) {y : V}
    (hy : y ∈ (popularAuxiliaryInput
      (canonicalDeferredLadder G kappa preferred)
      (canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
        hNoEnter)).targetMarkers) :
    y ∈ ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
      (canonicalLadder_isSplitLegal preferred hkappa huncountable
        hNoEnter)).targetMarkers := by
  rcases hy with ⟨hyMarker, hyEssential⟩
  refine ⟨?_, ?_⟩
  · change y ∈ (canonicalDeferredLadder G kappa preferred).markerSet at hyMarker
    change y ∈ (canonicalLadder G kappa preferred).markerSet
    exact hyMarker
  · change y ∈ G.vertexSet (G.essentialWarpPart
      (canonicalDeferredLadder G kappa preferred).limitWarp) at hyEssential
    change y ∈ G.vertexSet (G.essentialWarpPart
      (canonicalLadder G kappa preferred).limitWarp)
    exact hyEssential

/-- A deferred chosen component cannot be the current marker component, so
it lies in the arrow-only part of the canonical successor. -/
theorem canonicalDeferredLadder_chosen_mem_arrowPart
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a : Stage kappa} {p : G.DPath}
    (hchosen : (canonicalDeferredLadder G kappa preferred).chosen a = some p) :
    p ∈ (canonicalDeferredLadder G kappa preferred).arrowPart a := by
  let L := canonicalDeferredLadder G kappa preferred
  have hlegal : IsDeferredLegal L :=
    canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
      hNoEnter
  have hsplit : (canonicalLadder G kappa preferred).IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  have hpSpec := chosen_spec hlegal.validBookkeeping hchosen
  have hpSuccessor : p ∈ L.successorWarp a := hpSpec.1.1
  have hsuccessor : L.successorWarp a =
      L.arrowPart a ∪ L.markerPathSet a := by
    change (canonicalLadder G kappa preferred).successorWarp a =
      (canonicalLadder G kappa preferred).arrowPart a ∪
        (canonicalLadder G kappa preferred).markerPathSet a
    exact (hsplit.exactSuccessorArrows a).2
  rw [hsuccessor] at hpSuccessor
  rcases hpSuccessor with hpArrow | hpMarker
  · exact hpArrow
  · cases hm : L.marker a with
    | none =>
        exfalso
        simpa [markerPathSet, hm] using hpMarker
    | some y =>
        have hp : p = G.trivialPath y := by
          simpa [markerPathSet, hm] using hpMarker
        exfalso
        apply hpSpec.2
        rw [hm, hp]
        rfl

/-- Every vertex of a ray chosen by deferred bookkeeping lies in the strict
roof of the pre-marker arrow frontier. -/
theorem canonicalDeferredLadder_chosenRay_support_subset_strictRoof_arrowPart
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a : Stage kappa} (r : Ray G.graph)
    (hchosen : (canonicalDeferredLadder G kappa preferred).chosen a =
      some (.inr r : G.DPath)) :
    r.support ⊆ G.strictRoof (G.terminalFrontier
      ((canonicalDeferredLadder G kappa preferred).arrowPart a)) := by
  have hrArrow : (Sum.inr r : G.DPath) ∈
      (canonicalDeferredLadder G kappa preferred).arrowPart a :=
    canonicalDeferredLadder_chosen_mem_arrowPart preferred hkappa huncountable
      hNoEnter hchosen
  intro z hzr
  refine ⟨canonicalLadder_arrowPart_selfRoofing
      preferred hkappa huncountable hNoEnter a ⟨.inr r, hrArrow, hzr⟩, ?_⟩
  intro hzEssential
  obtain ⟨q, hqArrow, hqz⟩ := hzEssential.1
  have hsplit : (canonicalLadder G kappa preferred).IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  have hqr : q = (Sum.inr r : G.DPath) := by
    by_contra hne
    exact Set.disjoint_left.1 (hsplit.arrowPart_isWarp a
      hqArrow hrArrow hne) (G.terminal_mem_support hqz) hzr
  subst q
  simp at hqz

/-- Rung maximality prevents a finite deferred chosen component which is
essential in the pre-marker arrow from becoming inessential after adjoining
the current marker. -/
theorem canonicalDeferredLadder_no_chosenFinite_of_essential_arrowPart
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a : Stage kappa} (f : FinitePath G.graph)
    (hchosen : (canonicalDeferredLadder G kappa preferred).chosen a =
      some (.inl f : G.DPath))
    (hpEssential : (Sum.inl f : G.DPath) ∈ G.essentialWarpPart
      ((canonicalDeferredLadder G kappa preferred).arrowPart a))
    {y : V}
    (hmarker : (canonicalDeferredLadder G kappa preferred).marker a = some y) :
    False := by
  let L := canonicalDeferredLadder G kappa preferred
  have hlegal : IsDeferredLegal L :=
    canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
      hNoEnter
  have hsplit : (canonicalLadder G kappa preferred).IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  let A := G.terminalFrontier (L.warpAt a)
  let T := (L.stageWeb a).terminalFrontier (L.rung a)
  have hxArrow : f.finish ∈
      G.essential (G.terminalFrontier (L.arrowPart a)) := by
    obtain ⟨_, z, hzTerminal, hzEssential⟩ := hpEssential
    have hzx : z = f.finish := by
      exact (Option.some.inj hzTerminal).symm
    exact hzx ▸ hzEssential
  have hOldWarp : G.IsWarp (L.warpAt a) :=
    hlegal.warpStages (Stage.toExtended a)
  have hLiftWarp : G.IsWarp (L.liftedRung a) := by
    change G.IsWarp (L.liftStagePath a '' L.rung a)
    exact G.isWarp_liftLadderStageFamily (L.warpAt a)
      (hlegal.waveRungs a).1
  have hOldSelf : G.vertexSet (L.warpAt a) ⊆ G.roof A := by
    simpa only [A] using
      vertexSet_warpAt_subset_roof_terminalFrontier hlegal a
  have hLiftInitial : G.initialSet (L.liftedRung a) ⊆
      G.essential A := by
    have h := G.initialSet_liftLadderStageFamily_subset_essential
      (L.warpAt a) (hlegal.roofsSourceAtStages (Stage.toExtended a))
      (hlegal.waveRungs a).2.1
    change G.initialSet (L.liftStagePath a '' L.rung a) ⊆ G.essential A
    exact h
  have hEssRoofLift : G.essential A ⊆
      G.roof (G.terminalFrontier (L.liftedRung a)) := by
    have h := G.essential_subset_roof_terminalFrontier_liftLadderStageFamily
      hNoEnter (L.warpAt a) (hlegal.waveRungs a)
    change G.essential A ⊆ G.roof
      (G.terminalFrontier (L.liftStagePath a '' L.rung a))
    exact h
  have hOldRoofLift : G.roof A ⊆
      G.roof (G.terminalFrontier (L.liftedRung a)) := by
    rw [← G.roof_essential A]
    exact G.roof_cut hEssRoofLift
  have hOldCross : G.initialSet (L.warpAt a ∪ L.liftedRung a) ⊆
      G.roof A := by
    rw [G.initialSet_union]
    rintro z (hzOld | hzLift)
    · exact hOldSelf (G.initialSet_subset_vertexSet' _ hzOld)
    · exact G.essential_subset_roof A (hLiftInitial hzLift)
  have hLiftCross : G.initialSet (L.warpAt a ∪ L.liftedRung a) ⊆
      G.roof (G.terminalFrontier (L.liftedRung a)) := by
    rw [G.initialSet_union]
    rintro z (hzOld | hzLift)
    · exact hOldRoofLift (hOldSelf (G.initialSet_subset_vertexSet' _ hzOld))
    · exact hEssRoofLift (hLiftInitial hzLift)
  have hxUnion : f.finish ∈ G.essential (A ∪ T) := by
    have heq := G.essential_terminalFrontier_arrow_eq_union_of_crossRoof
      hOldWarp hLiftWarp hOldCross hLiftCross
    have harrow : L.arrowPart a = G.arrow (L.warpAt a) (L.liftedRung a) := by
      change (canonicalLadder G kappa preferred).arrowPart a = _
      exact hsplit.arrowPart_eq_arrow a
    rw [harrow, heq] at hxArrow
    simpa only [A, T, terminalFrontier_liftedRung] using hxArrow
  have hxStage : f.finish ∈ (L.stageWeb a).essential T := by
    change f.finish ∈
      ((canonicalLadder G kappa preferred).stageWeb a).essential
        (((canonicalLadder G kappa preferred).stageWeb a).terminalFrontier
          ((canonicalLadder G kappa preferred).rung a))
    apply stageEssential_of_ambientEssential_old_union_rung
      (canonicalLadder G kappa preferred) hsplit hNoEnter a
    simpa [A, T, L, canonicalDeferredLadder,
      Deferred.withValidBookkeeping, canonicalLadder,
      KappaLadder.withValidBookkeeping, KappaLadder.stageWeb,
      KappaLadder.warpAt] using hxUnion
  have hyCandidate : y ∈ L.markerCandidates a :=
    (hlegal.freshMarkers.2 a y hmarker).1
  have hxT : f.finish ∈ T := hxStage.1
  obtain ⟨r, hrRung, hrTerminal⟩ := hxT
  have hrEssential : r ∈
      (L.stageWeb a).essentialWarpPart (L.rung a) :=
    ⟨hrRung, f.finish, hrTerminal, hxStage⟩
  have hxStageMarker : f.finish ∈
      (L.stageWeb a).essential (T ∪ {y}) :=
    essential_terminal_insert_of_roofMaximal_wave
      (L.stageWeb a) (hlegal.waveRungs a) (hlegal.roofMaximalRungs a)
      hrRung hrTerminal hrEssential hyCandidate.1.1
      (fun hyRung ↦ hyCandidate.2 (Or.inr hyRung))
  have hxAmbientMarker : f.finish ∈ G.essential (A ∪ (T ∪ {y})) :=
    ambientEssential_union_of_stageEssential G A (T ∪ {y}) hxStageMarker
  have hpArrow : (Sum.inl f : G.DPath) ∈ L.arrowPart a :=
    canonicalDeferredLadder_chosen_mem_arrowPart preferred hkappa huncountable
      hNoEnter hchosen
  have hpSuccessor : (Sum.inl f : G.DPath) ∈ L.successorWarp a := by
    have hsuccessor : L.successorWarp a =
        L.arrowPart a ∪ L.markerPathSet a := by
      change (canonicalLadder G kappa preferred).successorWarp a =
        (canonicalLadder G kappa preferred).arrowPart a ∪
          (canonicalLadder G kappa preferred).markerPathSet a
      exact (hsplit.exactSuccessorArrows a).2
    rw [hsuccessor]
    exact Or.inl hpArrow
  have hxSuccessor : f.finish ∈ G.terminalFrontier (L.successorWarp a) :=
    ⟨Sum.inl f, hpSuccessor, rfl⟩
  have hSuccessorSubset : G.terminalFrontier (L.successorWarp a) ⊆
      A ∪ (T ∪ {y}) := by
    rintro z ⟨p, hp, hpz⟩
    have hsuccessor : L.successorWarp a =
        L.arrowPart a ∪ L.markerPathSet a := by
      change (canonicalLadder G kappa preferred).successorWarp a =
        (canonicalLadder G kappa preferred).arrowPart a ∪
          (canonicalLadder G kappa preferred).markerPathSet a
      exact (hsplit.exactSuccessorArrows a).2
    rw [hsuccessor] at hp
    rcases hp with hpArrow | hpMarker
    · have hz := G.terminalFrontier_arrow_subset_union
          (L.warpAt a) (L.liftedRung a)
          ⟨p, by
            have harrow : L.arrowPart a =
                G.arrow (L.warpAt a) (L.liftedRung a) := by
              change (canonicalLadder G kappa preferred).arrowPart a = _
              exact hsplit.arrowPart_eq_arrow a
            simpa only [harrow] using hpArrow, hpz⟩
      rcases hz with hzA | hzT
      · exact Or.inl hzA
      · exact Or.inr (Or.inl (by
          simpa only [T, terminalFrontier_liftedRung] using hzT))
    · have hpTrivial : p = G.trivialPath y := by
        change p ∈ L.markerPathSet a at hpMarker
        rw [markerPathSet, hmarker] at hpMarker
        simpa only [Set.mem_singleton_iff] using hpMarker
      subst p
      have hzy : z = y :=
        (Option.some.inj ((G.terminal?_trivialPath y).symm.trans hpz)).symm
      exact Or.inr (Or.inr (by simpa [hzy]))
  have hxSuccessorEssential : f.finish ∈
      G.essential (G.terminalFrontier (L.successorWarp a)) :=
    essential_of_mem_of_subset G hSuccessorSubset hxSuccessor hxAmbientMarker
  have hpInessential :=
    (chosen_spec hlegal.validBookkeeping hchosen).1
  exact hpInessential.2
    ⟨hpInessential.1, f.finish, rfl, hxSuccessorEssential⟩

/-- A finite deferred record admits no target-pure route to its retained
same-stage marker. -/
theorem canonicalDeferredLadder_no_chosenFinite_equalTargetPureRoute
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    {a : Stage kappa} (f : FinitePath G.graph)
    (hchosen : (canonicalDeferredLadder G kappa preferred).chosen a =
      some (.inl f : G.DPath))
    (q : FinitePath ((popularAuxiliaryInput
      (canonicalDeferredLadder G kappa preferred)
      (canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
        hNoEnter)).lambda.graph))
    (hs : q.start ∈ (popularAuxiliaryInput
      (canonicalDeferredLadder G kappa preferred)
      (canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
        hNoEnter)).lambda.source)
    (hpure : (popularAuxiliaryInput
      (canonicalDeferredLadder G kappa preferred)
      (canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
        hNoEnter)).IsTargetPure q)
    {y : V} (hqstart : q.start = .old f.finish)
    (hqfinish : q.finish = .old y)
    (hmarker : (canonicalDeferredLadder G kappa preferred).marker a = some y)
    (htarget : y ∈ (popularAuxiliaryInput
      (canonicalDeferredLadder G kappa preferred)
      (canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
        hNoEnter)).targetMarkers) : False := by
  let L := canonicalDeferredLadder G kappa preferred
  let hlegal : IsDeferredLegal L :=
    canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
      hNoEnter
  let J := popularAuxiliaryInput L hlegal
  have htargetSplit := deferredTargetMarker_mem_splitTargetMarkers
    preferred hkappa huncountable hNoEnter htarget
  have hpArrow : (Sum.inl f : G.DPath) ∈ L.arrowPart a :=
    canonicalDeferredLadder_chosen_mem_arrowPart preferred hkappa huncountable
      hNoEnter hchosen
  by_cases hpEssential : (Sum.inl f : G.DPath) ∈
      G.essentialWarpPart (L.arrowPart a)
  · exact canonicalDeferredLadder_no_chosenFinite_of_essential_arrowPart
      preferred hkappa huncountable hNoEnter f hchosen hpEssential hmarker
  · have hpInessential : (Sum.inl f : G.DPath) ∈
        G.inessentialPaths (L.arrowPart a) := ⟨hpArrow, hpEssential⟩
    have hxStrict : f.finish ∈
        G.strictRoof (G.terminalFrontier (L.arrowPart a)) := by
      apply G.terminal_mem_strictRoof_of_mem_inessentialPaths hpInessential
      rfl
    have hrun : PopularAuxiliary.Input.RunsFromTo f.finish y
        (J.decodeWalkSteps q.walk) :=
      J.decodeWalkSteps_runs_from_entry q.walk
        (by rw [hqstart]; rfl) (by rw [hqfinish]; rfl)
    have hyRoof : y ∈ G.roof (G.terminalFrontier (L.arrowPart a)) := by
      exact
        canonicalLadder_targetPure_run_terminal_mem_roof_arrowPartFrontier_of_ladder
          preferred hkappa huncountable hNoEnter J rfl a q hs hpure
            hrun hxStrict
    exact canonicalLadder_targetMarker_not_mem_roof_arrowPartFrontier
      preferred hkappa huncountable hNoEnter hmarker htargetSplit hyRoof

/-- A deferred ray proxy admits no target-pure route to its retained
same-stage marker. -/
theorem canonicalDeferredLadder_no_chosenRay_equalTargetPureRoute
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (i : infiniteRecords (canonicalDeferredLadder G kappa preferred))
    (r : Ray G.graph)
    (hir : i.1 = (.inr r : G.DPath))
    (q : FinitePath ((popularAuxiliaryInput
      (canonicalDeferredLadder G kappa preferred)
      (canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
        hNoEnter)).lambda.graph))
    (hs : q.start ∈ (popularAuxiliaryInput
      (canonicalDeferredLadder G kappa preferred)
      (canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
        hNoEnter)).lambda.source)
    (hpure : (popularAuxiliaryInput
      (canonicalDeferredLadder G kappa preferred)
      (canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
        hNoEnter)).IsTargetPure q)
    {y : V} (hqstart : q.start = .proxy i)
    (hqfinish : q.finish = .old y)
    (hmarker : (canonicalDeferredLadder G kappa preferred).marker
      (infiniteStage (canonicalDeferredLadder G kappa preferred) i) = some y)
    (htarget : y ∈ (popularAuxiliaryInput
      (canonicalDeferredLadder G kappa preferred)
      (canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
        hNoEnter)).targetMarkers) : False := by
  let L := canonicalDeferredLadder G kappa preferred
  let hlegal : IsDeferredLegal L :=
    canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
      hNoEnter
  let J := popularAuxiliaryInput L hlegal
  let a := infiniteStage L i
  have hiChosen : L.chosen a = some i.1 := (infiniteStage_spec L i).2
  have hrChosen : L.chosen a = some (.inr r : G.DPath) := by
    simpa only [hir] using hiChosen
  have htargetSplit := deferredTargetMarker_mem_splitTargetMarkers
    preferred hkappa huncountable hNoEnter htarget
  obtain ⟨z, hzProxy, hrun⟩ :=
    J.decodeWalkSteps_runs_from_eq_proxy q.walk hqstart
      (by rw [hqfinish]; rfl)
  have hzRay : z ∈ r.support := by
    change z ∈ i.1.support at hzProxy
    rwa [hir] at hzProxy
  have hzStrict : z ∈ G.strictRoof
      (G.terminalFrontier (L.arrowPart a)) :=
    canonicalDeferredLadder_chosenRay_support_subset_strictRoof_arrowPart
      preferred hkappa huncountable hNoEnter r hrChosen hzRay
  have hyRoof : y ∈ G.roof (G.terminalFrontier (L.arrowPart a)) := by
    exact
      canonicalLadder_targetPure_run_terminal_mem_roof_arrowPartFrontier_of_ladder
        preferred hkappa huncountable hNoEnter J rfl a q hs hpure
          hrun hzStrict
  exact canonicalLadder_targetMarker_not_mem_roof_arrowPartFrontier
    preferred hkappa huncountable hNoEnter hmarker htargetSplit hyRoof

/-- An equal deferred route starts at a finite record or a ray proxy and
ends at a target marker born at exactly the same stage. -/
theorem equalSubwarp_path_sameStage
    (L : G.KappaLadder kappa) (hL : IsKappaHindrance L)
    (P : Popular.XSWarp (popularAuxiliaryInput L hL.legal).lambda
      (popularAuxiliaryInput L hL.legal).lambda.target)
    {p : FinitePath (popularAuxiliaryInput L hL.legal).lambda.graph}
    (hp : p ∈ ((popularAuxiliaryIndexed L hL).equalSubwarp P).paths) :
    (∃ (x : finiteTerminalSet L)
      (y : (popularAuxiliaryInput L hL.legal).targetMarkers),
      p.start = .old x.1 ∧ p.finish = .old y.1 ∧
      L.markerStage ⟨y.1, y.2.1⟩ = finiteTerminalStage L x) ∨
    (∃ (i : infiniteRecords L)
      (y : (popularAuxiliaryInput L hL.legal).targetMarkers),
      p.start = .proxy i ∧ p.finish = .old y.1 ∧
      L.markerStage ⟨y.1, y.2.1⟩ = infiniteStage L i) := by
  let I := popularAuxiliaryInput L hL.legal
  let U := popularAuxiliaryIndexed L hL
  have hpSource : p.start ∈ I.lambda.source :=
    (U.equalSubwarp P).starts_in_source hp
  have hpTarget : p.finish ∈ I.lambda.target :=
    (U.equalSubwarp P).ends_in_target hp
  have hindex := U.equalSubwarp_index_eq P hp
  obtain ⟨y, hyTarget, hfinish⟩ := I.finish_of_mem_lambda_target p hpTarget
  let ys : I.targetMarkers := ⟨y, hyTarget⟩
  rcases I.start_of_mem_lambda_source p hpSource with
      ⟨x, hxFinite, hstart⟩ | ⟨i, hstart⟩
  · left
    let xs : finiteTerminalSet L := ⟨x, hxFinite⟩
    refine ⟨xs, ys, hstart, hfinish, ?_⟩
    have hs : U.f ⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ =
        U.f ⟨.old x, (I.mem_lambda_source_old x).2 hxFinite⟩ := by
      apply congrArg U.f
      exact Subtype.ext hstart
    have ht : U.g ⟨p.finish, (U.equalSubwarp P).ends_in_target hp⟩ =
        U.g ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ := by
      apply congrArg U.g
      exact Subtype.ext hfinish
    exact ht.symm.trans (hindex.trans hs)
  · right
    refine ⟨i, ys, hstart, hfinish, ?_⟩
    have hs : U.f ⟨p.start, (U.equalSubwarp P).starts_in_source hp⟩ =
        U.f ⟨.proxy i, I.mem_lambda_source_proxy i⟩ := by
      apply congrArg U.f
      exact Subtype.ext hstart
    have ht : U.g ⟨p.finish, (U.equalSubwarp P).ends_in_target hp⟩ =
        U.g ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ := by
      apply congrArg U.g
      exact Subtype.ext hfinish
    exact ht.symm.trans (hindex.trans hs)

/-- No target-pure member of an equal subwarp exists for the canonical
deferred ladder. -/
theorem canonicalDeferredLadder_no_targetPure_equalSubwarp_path
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder G kappa preferred))
    (P : Popular.XSWarp
      (popularAuxiliaryInput (canonicalDeferredLadder G kappa preferred)
        hL.legal).lambda
      (popularAuxiliaryInput (canonicalDeferredLadder G kappa preferred)
        hL.legal).lambda.target)
    {p : FinitePath
      (popularAuxiliaryInput (canonicalDeferredLadder G kappa preferred)
        hL.legal).lambda.graph}
    (hp : p ∈ ((popularAuxiliaryIndexed
      (canonicalDeferredLadder G kappa preferred) hL).equalSubwarp P).paths)
    (hpure : (popularAuxiliaryInput
      (canonicalDeferredLadder G kappa preferred) hL.legal).IsTargetPure p) :
    False := by
  let L := canonicalDeferredLadder G kappa preferred
  let I := popularAuxiliaryInput L hL.legal
  have hpSource : p.start ∈ I.lambda.source :=
    ((popularAuxiliaryIndexed L hL).equalSubwarp P).starts_in_source hp
  rcases equalSubwarp_path_sameStage L hL P hp with
      ⟨x, y, hstart, hfinish, hstage⟩ |
      ⟨i, y, hstart, hfinish, hstage⟩
  · obtain ⟨_, q, hchosen, hterminal⟩ := finiteTerminalStage_spec L x
    rcases q with f | r
    · have hfx : f.finish = x.1 := Option.some.inj hterminal
      have hmarker : L.marker (finiteTerminalStage L x) = some y.1 := by
        rw [← hstage]
        exact L.markerStage_spec ⟨y.1, y.2.1⟩
      exact canonicalDeferredLadder_no_chosenFinite_equalTargetPureRoute
        preferred hkappa huncountable hNoEnter f hchosen p hpSource hpure
        (by simpa only [hfx] using hstart) hfinish hmarker y.2
    · simp at hterminal
  · obtain ⟨r, hir⟩ := infinitePath_isRay L hL.legal i
    have hmarker : L.marker (infiniteStage L i) = some y.1 := by
      rw [← hstage]
      exact L.markerStage_spec ⟨y.1, y.2.1⟩
    exact canonicalDeferredLadder_no_chosenRay_equalTargetPureRoute
      preferred hkappa huncountable hNoEnter i r hir p hpSource hpure
      hstart hfinish hmarker y.2

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.canonicalDeferredLadder_no_targetPure_equalSubwarp_path
