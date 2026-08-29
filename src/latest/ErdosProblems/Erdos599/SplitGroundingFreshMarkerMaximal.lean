/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingFreshPreMarker

/-!
# Maximal-rung exclusion of a fresh same-stage marker route

The pre-marker analysis reduces a finite fresh equal route to a precise
configuration: its record component is essential in the exact rung arrow,
but the new marker makes it inessential in the full successor.  This file
rules out that configuration using the roof maximality of the canonical
rung.  The argument does not assume that the rung is full.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- Restricting a web to target-reachable vertices does not change roofs. -/
private theorem roof_essentialPart_local
    (Q : DWeb V) (S : Set V) :
    Q.essentialPart.roof S = Q.roof S := by
  apply Set.Subset.antisymm
  · intro x hx p hp
    have hreach : p.support ⊆ Q.reachableToTarget :=
      Q.finitePath_support_subset_reachableToTarget p hp.2
    let hrestrict : ∀ {a b : V}, Q.graph.Adj a b →
        a ∈ p.support → b ∈ p.support →
          Q.essentialPart.graph.Adj a b :=
      fun e ha hb ↦ ⟨e, hreach ha, hreach hb⟩
    let q : FinitePath Q.essentialPart.graph :=
      p.restrictGraphOnSupport hrestrict
    have hqTarget : Q.essentialPart.IsTargetPathFrom x q := by
      refine ⟨hp.1, hp.2⟩
    obtain ⟨z, hzq, hzS⟩ := hx q hqTarget
    refine ⟨z, ?_, hzS⟩
    have hsupp : q.support = p.support :=
      FinitePath.support_restrictGraphOnSupport p hrestrict
    rwa [hsupp] at hzq
  · intro x hx p hp
    let q : FinitePath Q.graph :=
      p.lift (fun {_ _} e ↦ Q.essentialPart_adj_imp e)
    obtain ⟨z, hzq, hzS⟩ := hx q ⟨hp.1, hp.2⟩
    refine ⟨z, ?_, hzS⟩
    simpa only [q, FinitePath.support_lift] using hzq

private theorem strictRoof_essentialPart_local
    (Q : DWeb V) (S : Set V) :
    Q.essentialPart.strictRoof S = Q.strictRoof S := by
  unfold DWeb.strictRoof
  rw [roof_essentialPart_local]
  congr 1
  ext x
  change (x ∈ S ∧ x ∉ Q.essentialPart.roof (S \ {x})) ↔
    (x ∈ S ∧ x ∉ Q.roof (S \ {x}))
  rw [roof_essentialPart_local]

/-- Essentiality for a larger cut descends to a smaller cut containing the
point. -/
theorem essential_of_mem_of_subset
    (Q : DWeb V) {S R : Set V} (hSR : S ⊆ R) {x : V}
    (hxS : x ∈ S) (hxR : x ∈ Q.essential R) :
    x ∈ Q.essential S := by
  refine ⟨hxS, ?_⟩
  intro hxRoof
  apply hxR.2
  apply Q.roof_mono ?_ hxRoof
  intro z hz
  exact ⟨hSR hz.1, hz.2⟩

/-- The two canonical lifts do not change the terminal frontier of a rung. -/
theorem terminalFrontier_liftedRung
    (L : G.KappaLadder kappa) (a : Ladder.Stage kappa) :
    G.terminalFrontier (L.liftedRung a) =
      (L.stageWeb a).terminalFrontier (L.rung a) := by
  ext x
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, hqx⟩
    exact ⟨r, hr, by simpa using hqx⟩
  · rintro ⟨r, hr, hrx⟩
    exact ⟨L.liftStagePath a r, ⟨r, hr, rfl⟩, by simpa using hrx⟩

/-- A point essential for the old-frontier/rung-frontier union is essential
for the rung frontier in the essential quotient stage. -/
theorem stageEssential_of_ambientEssential_old_union_rung_of_wave
    (L : G.KappaLadder kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : Ladder.Stage kappa) (hWave : (L.stageWeb a).IsWave (L.rung a)) {x : V}
    (hx : x ∈ G.essential
      (G.terminalFrontier (L.warpAt a) ∪
        (L.stageWeb a).terminalFrontier (L.rung a))) :
    x ∈ (L.stageWeb a).essential
      ((L.stageWeb a).terminalFrontier (L.rung a)) := by
  let A := G.terminalFrontier (L.warpAt a)
  let T := (L.stageWeb a).terminalFrontier (L.rung a)
  have hEssRoof : G.essential A ⊆ G.roof T := by
    have h := G.essential_subset_roof_terminalFrontier_liftLadderStageFamily
      hNoEnter (L.warpAt a) hWave
    change G.essential A ⊆
      G.roof (G.terminalFrontier (L.liftedRung a)) at h
    rw [terminalFrontier_liftedRung] at h
    exact h
  have hxT : x ∈ T := by
    by_contra hxNotT
    have hxRoofT : x ∈ G.roof T := by
      rcases hx.1 with hxA | hxT
      · exact hEssRoof
          (essential_of_mem_of_subset G Set.subset_union_left hxA hx)
      · exact (hxNotT hxT).elim
    have hxStrictT : x ∈ G.strictRoof T :=
      ⟨hxRoofT, fun hxEss ↦ hxNotT hxEss.1⟩
    exact Set.disjoint_left.1
      (G.disjoint_essential_union_strictRoof_left T A)
      (by simpa only [A, T, Set.union_comm] using hx) hxStrictT
  change x ∈ (G.quotient A).essentialPart.essential T
  refine ⟨hxT, ?_⟩
  intro hxRoof
  have hxNotMem : x ∉ T \ {x} := by simp
  have hxStrictStage : x ∈
      (G.quotient A).essentialPart.strictRoof (T \ {x}) :=
    ⟨hxRoof, fun hxEss ↦ hxNotMem hxEss.1⟩
  have hxStrictAmbient : x ∈ G.strictRoof (A ∪ (T \ {x})) := by
    rw [strictRoof_essentialPart_local,
      G.strictRoof_quotient_eq_strictRoof_union] at hxStrictStage
    exact hxStrictStage
  by_cases hxA : x ∈ A
  · have hset : A ∪ (T \ {x}) = A ∪ T := by
      ext z
      constructor
      · rintro (hzA | ⟨hzT, _⟩)
        · exact Or.inl hzA
        · exact Or.inr hzT
      · rintro (hzA | hzT)
        · exact Or.inl hzA
        · by_cases hzx : z = x
          · exact Or.inl (hzx ▸ hxA)
          · exact Or.inr ⟨hzT, hzx⟩
    rw [hset] at hxStrictAmbient
    exact hxStrictAmbient.2 hx
  · apply hx.2
    have hset : A ∪ (T \ {x}) = (A ∪ T) \ {x} := by
      ext z
      simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
      aesop
    rw [hset] at hxStrictAmbient
    exact hxStrictAmbient.1

/-- Legacy split legality supplies the wave input of the marker-independent
essentiality transport theorem. -/
theorem stageEssential_of_ambientEssential_old_union_rung
    (L : G.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : Ladder.Stage kappa) {x : V}
    (hx : x ∈ G.essential
      (G.terminalFrontier (L.warpAt a) ∪
        (L.stageWeb a).terminalFrontier (L.rung a))) :
    x ∈ (L.stageWeb a).essential
      ((L.stageWeb a).terminalFrontier (L.rung a)) :=
  L.stageEssential_of_ambientEssential_old_union_rung_of_wave
    hNoEnter a (hlegal.waveRungs a) hx

/-- Essentiality in an essential quotient stage lifts to essentiality after
re-adjoining the old commitment set.  The quotient path cannot enter that
old set after its initial vertex. -/
theorem ambientEssential_union_of_stageEssential
    (Q : DWeb V) (A M : Set V) {x : V}
    (hx : x ∈ (Q.quotient A).essentialPart.essential M) :
    x ∈ Q.essential (A ∪ M) := by
  refine ⟨Or.inr hx.1, ?_⟩
  obtain ⟨p, hpTarget, hpAvoid⟩ :=
    ((Q.quotient A).essentialPart.not_mem_roof_iff
      (M \ {x}) x).1 hx.2
  let q : FinitePath (Q.quotient A).graph :=
    p.lift (fun {_ _} e ↦ (Q.quotient A).essentialPart_adj_imp e)
  let r : FinitePath Q.graph :=
    q.lift (fun {_ _} e ↦ Q.quotient_adj_imp e)
  apply (Q.not_mem_roof_iff ((A ∪ M) \ {x}) x).2
  refine ⟨r, ⟨hpTarget.1, hpTarget.2⟩, ?_⟩
  apply Set.disjoint_left.2
  intro z hzr hzCut
  have hzq : z ∈ q.support := by
    simpa only [r, FinitePath.support_lift] using hzr
  have hzp : z ∈ p.support := by
    simpa only [q, FinitePath.support_lift] using hzq
  rcases hzCut.1 with hzA | hzM
  · rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
        (Q.quotient A).graph.Adj q.walk).1 hzq with hzStart | hzTail
    · exact hzCut.2 (hzStart.trans hpTarget.1)
    · exact (Q.quotientWalk_tail_avoids q.walk hzTail).2 hzA
  · exact Set.disjoint_left.1 hpAvoid hzp ⟨hzM, hzCut.2⟩

/-- A ray record born at a fresh stage is confined to the strict
pre-marker arrow roof.  Hence no target-pure route from its auxiliary proxy
can reach the retained marker born at that same stage. -/
theorem canonicalLadder_no_freshRay_equalTargetPureRoute
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : (canonicalLadder G kappa preferred).freshInessentialGroundStages)
    (r : Ray G.graph)
    (hrecord :
      (canonicalLadder G kappa preferred).freshGroundRecordPath
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter) a = .inr r)
    (q : FinitePath
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).lambda.graph)
    (hs : q.start ∈
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).lambda.source)
    (hpure :
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).IsTargetPure q)
    (i : (canonicalLadder G kappa preferred).splitInfiniteRecords)
    (hqstart : q.start = .proxy i) {y : V}
    (hqfinish : q.finish = .old y)
    (hiStage :
      (canonicalLadder G kappa preferred).splitInfiniteStage i = a.1)
    (hmarker : (canonicalLadder G kappa preferred).marker a.1 = some y)
    (htarget : y ∈
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).targetMarkers) :
    False := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  let I := L.splitPopularAuxiliaryInput hlegal
  change L.freshGroundRecordPath hlegal a = .inr r at hrecord
  change q.start ∈ I.lambda.source at hs
  change I.IsTargetPure q at hpure
  change L.splitInfiniteStage i = a.1 at hiStage
  change L.marker a.1 = some y at hmarker
  change y ∈ I.targetMarkers at htarget
  have hiChosen : L.chosen a.1 = some i.1 := by
    rw [← hiStage]
    exact (L.splitInfiniteStage_spec i).2
  have hiRecord : i.1 = (Sum.inr r : G.DPath) := by
    apply Option.some.inj
    rw [← hrecord]
    exact hiChosen.symm.trans (L.chosen_freshGroundRecordPath hlegal a)
  have hproxy : I.proxyPath i = (Sum.inr r : G.DPath) := by
    change L.splitInfinitePath hlegal i = (Sum.inr r : G.DPath)
    simpa only [splitInfinitePath] using hiRecord
  obtain ⟨z, hzProxy, hrun⟩ :=
    I.decodeWalkSteps_runs_from_eq_proxy q.walk hqstart (by
      rw [hqfinish]
      rfl)
  have hzRay : z ∈ r.support := by
    rw [hproxy] at hzProxy
    exact hzProxy
  have hzStrict : z ∈ G.strictRoof
      (G.terminalFrontier (L.arrowPart a.1)) :=
    canonicalLadder_freshRay_support_subset_strictRoof_arrowPartFrontier
      preferred hkappa huncountable hNoEnter a r hrecord hzRay
  have hyRoof : y ∈ G.roof
      (G.terminalFrontier (L.arrowPart a.1)) :=
    canonicalLadder_targetPure_run_terminal_mem_roof_arrowPartFrontier
      preferred hkappa huncountable hNoEnter a.1 q hs hpure hrun hzStrict
  exact canonicalLadder_targetMarker_not_mem_roof_arrowPartFrontier
    preferred hkappa huncountable hNoEnter hmarker htarget hyRoof

/-- The route-independent maximal-rung contradiction for a finite fresh
record.  Once that record remains essential in the pre-marker arrow, the
new marker cannot make it inessential in the full successor. -/
theorem canonicalLadder_no_freshFinite_of_essential_arrowPart
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : (canonicalLadder G kappa preferred).freshInessentialGroundStages)
    (f : FinitePath G.graph)
    (hrecord :
      (canonicalLadder G kappa preferred).freshGroundRecordPath
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter) a = .inl f)
    (hpEssential :
      (canonicalLadder G kappa preferred).freshGroundRecordPath
          (canonicalLadder_isSplitLegal preferred hkappa huncountable
            hNoEnter) a ∈
        G.essentialWarpPart
          ((canonicalLadder G kappa preferred).arrowPart a.1))
    {y : V}
    (hmarker : (canonicalLadder G kappa preferred).marker a.1 = some y) :
    False := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  change L.freshGroundRecordPath hlegal a = .inl f at hrecord
  change L.freshGroundRecordPath hlegal a ∈
    G.essentialWarpPart (L.arrowPart a.1) at hpEssential
  change L.marker a.1 = some y at hmarker
  let A := G.terminalFrontier (L.warpAt a.1)
  let T := (L.stageWeb a.1).terminalFrontier (L.rung a.1)
  have hxArrow : f.finish ∈
      G.essential (G.terminalFrontier (L.arrowPart a.1)) := by
    obtain ⟨_, z, hzTerminal, hzEssential⟩ := hpEssential
    have hzx : z = f.finish := by
      rw [hrecord] at hzTerminal
      exact (Option.some.inj hzTerminal).symm
    exact hzx ▸ hzEssential
  have hOldWarp : G.IsWarp (L.warpAt a.1) :=
    hlegal.warpStages (Ladder.Stage.toExtended a.1)
  have hLiftWarp : G.IsWarp (L.liftedRung a.1) := by
    change G.IsWarp (L.liftStagePath a.1 '' L.rung a.1)
    exact G.isWarp_liftLadderStageFamily (L.warpAt a.1)
      (hlegal.waveRungs a.1).1
  have hOldSelf : G.vertexSet (L.warpAt a.1) ⊆ G.roof A := by
    simpa only [A] using
      hlegal.vertexSet_warpAt_subset_roof_terminalFrontier a.1
  have hLiftInitial : G.initialSet (L.liftedRung a.1) ⊆
      G.essential A := by
    have h := G.initialSet_liftLadderStageFamily_subset_essential
      (L.warpAt a.1)
      (hlegal.roofsSourceAtStages (Ladder.Stage.toExtended a.1))
      (hlegal.waveRungs a.1).2.1
    change G.initialSet (L.liftStagePath a.1 '' L.rung a.1) ⊆
      G.essential A
    exact h
  have hEssRoofLift : G.essential A ⊆
      G.roof (G.terminalFrontier (L.liftedRung a.1)) := by
    have h := G.essential_subset_roof_terminalFrontier_liftLadderStageFamily
      hNoEnter (L.warpAt a.1) (hlegal.waveRungs a.1)
    change G.essential A ⊆
      G.roof (G.terminalFrontier
        (L.liftStagePath a.1 '' L.rung a.1))
    exact h
  have hOldRoofLift : G.roof A ⊆
      G.roof (G.terminalFrontier (L.liftedRung a.1)) := by
    rw [← G.roof_essential A]
    exact G.roof_cut hEssRoofLift
  have hOldCross : G.initialSet (L.warpAt a.1 ∪ L.liftedRung a.1) ⊆
      G.roof A := by
    rw [G.initialSet_union]
    rintro z (hzOld | hzLift)
    · exact hOldSelf (G.initialSet_subset_vertexSet' _ hzOld)
    · exact G.essential_subset_roof A (hLiftInitial hzLift)
  have hLiftCross : G.initialSet (L.warpAt a.1 ∪ L.liftedRung a.1) ⊆
      G.roof (G.terminalFrontier (L.liftedRung a.1)) := by
    rw [G.initialSet_union]
    rintro z (hzOld | hzLift)
    · exact hOldRoofLift
        (hOldSelf (G.initialSet_subset_vertexSet' _ hzOld))
    · exact hEssRoofLift (hLiftInitial hzLift)
  have hxUnion : f.finish ∈ G.essential (A ∪ T) := by
    have heq := G.essential_terminalFrontier_arrow_eq_union_of_crossRoof
      hOldWarp hLiftWarp hOldCross hLiftCross
    rw [hlegal.arrowPart_eq_arrow a.1, heq] at hxArrow
    simpa only [A, T, terminalFrontier_liftedRung] using hxArrow
  have hxStage : f.finish ∈ (L.stageWeb a.1).essential T := by
    exact stageEssential_of_ambientEssential_old_union_rung
      L hlegal hNoEnter a.1 hxUnion
  have hyCandidate : y ∈ L.markerCandidates a.1 :=
    (hlegal.freshMarkers.2 a.1 y hmarker).1
  have hxT : f.finish ∈ T := hxStage.1
  obtain ⟨r, hrRung, hrTerminal⟩ := hxT
  have hrEssential : r ∈
      (L.stageWeb a.1).essentialWarpPart (L.rung a.1) :=
    ⟨hrRung, f.finish, hrTerminal, hxStage⟩
  have hxStageMarker : f.finish ∈
      (L.stageWeb a.1).essential (T ∪ {y}) := by
    exact essential_terminal_insert_of_roofMaximal_wave
      (L.stageWeb a.1) (hlegal.waveRungs a.1)
      (hlegal.roofMaximalRungs a.1) hrRung hrTerminal hrEssential
      hyCandidate.1.1 (fun hyRung ↦ hyCandidate.2 (Or.inr hyRung))
  have hxAmbientMarker : f.finish ∈ G.essential (A ∪ (T ∪ {y})) := by
    exact ambientEssential_union_of_stageEssential G A (T ∪ {y})
      hxStageMarker
  have hpArrow : (Sum.inl f : G.DPath) ∈ L.arrowPart a.1 := by
    rw [← hrecord]
    exact L.freshGroundRecordPath_mem_arrowPart hlegal a
  have hpSuccessor : (Sum.inl f : G.DPath) ∈ L.successorWarp a.1 := by
    rw [(hlegal.exactSuccessorArrows a.1).2]
    exact Or.inl hpArrow
  have hxSuccessor : f.finish ∈ G.terminalFrontier (L.successorWarp a.1) :=
    ⟨Sum.inl f, hpSuccessor, rfl⟩
  have hSuccessorSubset : G.terminalFrontier (L.successorWarp a.1) ⊆
      A ∪ (T ∪ {y}) := by
    rintro z ⟨p, hp, hpz⟩
    rw [(hlegal.exactSuccessorArrows a.1).2] at hp
    rcases hp with hpArrow | hpMarker
    · have hz := G.terminalFrontier_arrow_subset_union
          (L.warpAt a.1) (L.liftedRung a.1)
          ⟨p, by simpa only [hlegal.arrowPart_eq_arrow a.1] using hpArrow, hpz⟩
      rcases hz with hzA | hzT
      · exact Or.inl hzA
      · exact Or.inr (Or.inl (by
          simpa only [T, terminalFrontier_liftedRung] using hzT))
    · have hpTrivial : p = G.trivialPath y := by
        simpa only [markerPathSet, hmarker, Set.mem_singleton_iff] using hpMarker
      subst p
      have hzy : z = y := by
        exact (Option.some.inj
          ((G.terminal?_trivialPath y).symm.trans hpz)).symm
      exact Or.inr (Or.inr (by simpa [hzy]))
  have hxSuccessorEssential : f.finish ∈
      G.essential (G.terminalFrontier (L.successorWarp a.1)) :=
    essential_of_mem_of_subset G hSuccessorSubset hxSuccessor hxAmbientMarker
  obtain ⟨p, hpChosen, hpInessential, _hpNotCurrent, _hpNotRecorded⟩ :=
    L.freshInessentialRecordStages_spec hlegal.validBookkeeping a.2.2
  have hpfresh : p = L.freshGroundRecordPath hlegal a :=
    Option.some.inj (hpChosen.symm.trans
      (L.chosen_freshGroundRecordPath hlegal a))
  subst p
  exact hpInessential.2
    ⟨hpInessential.1, f.finish, by simpa [hrecord], hxSuccessorEssential⟩

/-- A finite fresh grounded record cannot have a target-pure auxiliary
route to the marker born at its own stage. -/
theorem canonicalLadder_no_freshFinite_equalTargetPureRoute
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (a : (canonicalLadder G kappa preferred).freshInessentialGroundStages)
    (f : FinitePath G.graph)
    (hrecord :
      (canonicalLadder G kappa preferred).freshGroundRecordPath
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter) a = .inl f)
    (q : FinitePath
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).lambda.graph)
    (hs : q.start ∈
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).lambda.source)
    (hpure :
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).IsTargetPure q)
    {y : V} (hqstart : q.start = .old f.finish)
    (hqfinish : q.finish = .old y)
    (hmarker : (canonicalLadder G kappa preferred).marker a.1 = some y)
    (htarget : y ∈
      ((canonicalLadder G kappa preferred).splitPopularAuxiliaryInput
        (canonicalLadder_isSplitLegal preferred hkappa huncountable
          hNoEnter)).targetMarkers) :
    False := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  change L.freshGroundRecordPath hlegal a = .inl f at hrecord
  change q.start ∈ (L.splitPopularAuxiliaryInput hlegal).lambda.source at hs
  change (L.splitPopularAuxiliaryInput hlegal).IsTargetPure q at hpure
  change L.marker a.1 = some y at hmarker
  change y ∈ (L.splitPopularAuxiliaryInput hlegal).targetMarkers at htarget
  let A := G.terminalFrontier (L.warpAt a.1)
  let T := (L.stageWeb a.1).terminalFrontier (L.rung a.1)
  have hpEssential : L.freshGroundRecordPath hlegal a ∈
      G.essentialWarpPart (L.arrowPart a.1) :=
    canonicalLadder_freshFinite_equalRoute_mem_essential_arrowPart
      preferred hkappa huncountable hNoEnter a f hrecord q hs hpure
      hqstart hqfinish hmarker htarget
  have hxArrow : f.finish ∈
      G.essential (G.terminalFrontier (L.arrowPart a.1)) := by
    obtain ⟨_, z, hzTerminal, hzEssential⟩ := hpEssential
    have hzx : z = f.finish := by
      rw [hrecord] at hzTerminal
      exact (Option.some.inj hzTerminal).symm
    exact hzx ▸ hzEssential
  have hOldWarp : G.IsWarp (L.warpAt a.1) :=
    hlegal.warpStages (Ladder.Stage.toExtended a.1)
  have hLiftWarp : G.IsWarp (L.liftedRung a.1) := by
    change G.IsWarp (L.liftStagePath a.1 '' L.rung a.1)
    exact G.isWarp_liftLadderStageFamily (L.warpAt a.1)
      (hlegal.waveRungs a.1).1
  have hOldSelf : G.vertexSet (L.warpAt a.1) ⊆ G.roof A := by
    simpa only [A] using
      hlegal.vertexSet_warpAt_subset_roof_terminalFrontier a.1
  have hLiftInitial : G.initialSet (L.liftedRung a.1) ⊆
      G.essential A := by
    have h := G.initialSet_liftLadderStageFamily_subset_essential
      (L.warpAt a.1)
      (hlegal.roofsSourceAtStages (Ladder.Stage.toExtended a.1))
      (hlegal.waveRungs a.1).2.1
    change G.initialSet (L.liftStagePath a.1 '' L.rung a.1) ⊆
      G.essential A
    exact h
  have hEssRoofLift : G.essential A ⊆
      G.roof (G.terminalFrontier (L.liftedRung a.1)) := by
    have h := G.essential_subset_roof_terminalFrontier_liftLadderStageFamily
      hNoEnter (L.warpAt a.1) (hlegal.waveRungs a.1)
    change G.essential A ⊆
      G.roof (G.terminalFrontier
        (L.liftStagePath a.1 '' L.rung a.1))
    exact h
  have hOldRoofLift : G.roof A ⊆
      G.roof (G.terminalFrontier (L.liftedRung a.1)) := by
    rw [← G.roof_essential A]
    exact G.roof_cut hEssRoofLift
  have hOldCross : G.initialSet (L.warpAt a.1 ∪ L.liftedRung a.1) ⊆
      G.roof A := by
    rw [G.initialSet_union]
    rintro z (hzOld | hzLift)
    · exact hOldSelf (G.initialSet_subset_vertexSet' _ hzOld)
    · exact G.essential_subset_roof A (hLiftInitial hzLift)
  have hLiftCross : G.initialSet (L.warpAt a.1 ∪ L.liftedRung a.1) ⊆
      G.roof (G.terminalFrontier (L.liftedRung a.1)) := by
    rw [G.initialSet_union]
    rintro z (hzOld | hzLift)
    · exact hOldRoofLift
        (hOldSelf (G.initialSet_subset_vertexSet' _ hzOld))
    · exact hEssRoofLift (hLiftInitial hzLift)
  have hxUnion : f.finish ∈ G.essential (A ∪ T) := by
    have heq := G.essential_terminalFrontier_arrow_eq_union_of_crossRoof
      hOldWarp hLiftWarp hOldCross hLiftCross
    rw [hlegal.arrowPart_eq_arrow a.1, heq] at hxArrow
    simpa only [A, T, terminalFrontier_liftedRung] using hxArrow
  have hxStage : f.finish ∈ (L.stageWeb a.1).essential T := by
    exact stageEssential_of_ambientEssential_old_union_rung
      L hlegal hNoEnter a.1 hxUnion
  have hyCandidate : y ∈ L.markerCandidates a.1 :=
    (hlegal.freshMarkers.2 a.1 y hmarker).1
  have hxT : f.finish ∈ T := hxStage.1
  obtain ⟨r, hrRung, hrTerminal⟩ := hxT
  have hrEssential : r ∈
      (L.stageWeb a.1).essentialWarpPart (L.rung a.1) :=
    ⟨hrRung, f.finish, hrTerminal, hxStage⟩
  have hxStageMarker : f.finish ∈
      (L.stageWeb a.1).essential (T ∪ {y}) := by
    exact essential_terminal_insert_of_roofMaximal_wave
      (L.stageWeb a.1) (hlegal.waveRungs a.1)
      (hlegal.roofMaximalRungs a.1) hrRung hrTerminal hrEssential
      hyCandidate.1.1 (fun hyRung ↦ hyCandidate.2 (Or.inr hyRung))
  have hxAmbientMarker : f.finish ∈ G.essential (A ∪ (T ∪ {y})) := by
    exact ambientEssential_union_of_stageEssential G A (T ∪ {y})
      hxStageMarker
  have hpArrow : (Sum.inl f : G.DPath) ∈ L.arrowPart a.1 := by
    rw [← hrecord]
    exact L.freshGroundRecordPath_mem_arrowPart hlegal a
  have hpSuccessor : (Sum.inl f : G.DPath) ∈ L.successorWarp a.1 := by
    rw [(hlegal.exactSuccessorArrows a.1).2]
    exact Or.inl hpArrow
  have hxSuccessor : f.finish ∈ G.terminalFrontier (L.successorWarp a.1) :=
    ⟨Sum.inl f, hpSuccessor, rfl⟩
  have hSuccessorSubset : G.terminalFrontier (L.successorWarp a.1) ⊆
      A ∪ (T ∪ {y}) := by
    rintro z ⟨p, hp, hpz⟩
    rw [(hlegal.exactSuccessorArrows a.1).2] at hp
    rcases hp with hpArrow | hpMarker
    · have hz := G.terminalFrontier_arrow_subset_union
          (L.warpAt a.1) (L.liftedRung a.1)
          ⟨p, by simpa only [hlegal.arrowPart_eq_arrow a.1] using hpArrow, hpz⟩
      rcases hz with hzA | hzT
      · exact Or.inl hzA
      · exact Or.inr (Or.inl (by
          simpa only [T, terminalFrontier_liftedRung] using hzT))
    · have hpTrivial : p = G.trivialPath y := by
        simpa only [markerPathSet, hmarker, Set.mem_singleton_iff] using hpMarker
      subst p
      have hzy : z = y := by
        exact (Option.some.inj
          ((G.terminal?_trivialPath y).symm.trans hpz)).symm
      exact Or.inr (Or.inr (by simpa [hzy]))
  have hxSuccessorEssential : f.finish ∈
      G.essential (G.terminalFrontier (L.successorWarp a.1)) :=
    essential_of_mem_of_subset G hSuccessorSubset hxSuccessor hxAmbientMarker
  obtain ⟨p, hpChosen, hpInessential, _hpNotCurrent, _hpNotRecorded⟩ :=
    L.freshInessentialRecordStages_spec hlegal.validBookkeeping a.2.2
  have hpfresh : p = L.freshGroundRecordPath hlegal a :=
    Option.some.inj (hpChosen.symm.trans
      (L.chosen_freshGroundRecordPath hlegal a))
  subst p
  exact hpInessential.2
    ⟨hpInessential.1, f.finish, by simpa [hrecord], hxSuccessorEssential⟩

end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.canonicalLadder_no_freshFinite_equalTargetPureRoute
