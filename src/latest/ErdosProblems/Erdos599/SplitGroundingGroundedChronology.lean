/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedHangingRank

/-!
# Successor chronology for the grounded split auxiliary

The split separator branch uses only records selected at `phiGround`.
This file proves the target-pure successor-roof transport directly for that
grounded input.  In particular it does not coerce split legality to legacy
legality and does not enlarge a local grounded fan to the all-record input.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath Ladder Stationary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A grounded finite terminal inherits the strict successor-roof theorem
from its underlying finite obstruction record. -/
theorem splitGroundedFiniteTerminal_mem_strictRoof_successorFrontier
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (x : L.groundedFiniteTerminalSet) :
    x.1 ∈ Gamma.strictRoof
      (L.frontier (L.splitSuccessorStage hlegal (L.finiteTerminalIndex x))) := by
  let x' : L.finiteTerminalSet :=
    ⟨x.1, L.groundedFiniteTerminalSet_subset_finiteTerminalSet x.2⟩
  simpa only [finiteTerminalIndex] using
    L.splitFiniteTerminal_mem_strictRoof_successorFrontier hlegal x'

/-- A grounded ray record is also an all-record split ray record. -/
def groundedInfiniteRecordToSplit
    (L : Gamma.KappaLadder kappa) (i : L.groundedInfiniteRecords) :
    L.splitInfiniteRecords :=
  ⟨i.1, by
    obtain ⟨a, ha, hchosen⟩ := i.2
    exact ⟨a, ha.2, hchosen⟩⟩

@[simp]
theorem groundedInfiniteRecordToSplit_val
    (L : Gamma.KappaLadder kappa) (i : L.groundedInfiniteRecords) :
    (L.groundedInfiniteRecordToSplit i).1 = i.1 := rfl

theorem splitInfiniteStage_groundedInfiniteRecordToSplit
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (i : L.groundedInfiniteRecords) :
    L.splitInfiniteStage (L.groundedInfiniteRecordToSplit i) =
      L.groundedInfiniteStage i := by
  apply L.bookkeeping.chosen_stage_unique hlegal.validBookkeeping
  · exact (L.splitInfiniteStage_spec (L.groundedInfiniteRecordToSplit i)).2
  · exact (L.groundedInfiniteStage_spec i).2

/-- The proxy path of a grounded record lies in the strict roof immediately
after its selecting stage. -/
theorem splitGroundedPopularAuxiliary_proxyPath_support_subset_strictRoof
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (i : L.groundedInfiniteRecords) :
    ((L.splitGroundedPopularAuxiliaryInput hlegal).proxyPath i).support ⊆
      Gamma.strictRoof
        (L.frontier
          (L.splitSuccessorStage hlegal (L.groundedInfiniteStage i))) := by
  let j := L.groundedInfiniteRecordToSplit i
  have hj := L.splitInfinitePath_support_subset_strictRoof_successorFrontier
    hlegal j
  have hstage : L.splitInfiniteStage j = L.groundedInfiniteStage i := by
    simpa only [j] using
      L.splitInfiniteStage_groundedInfiniteRecordToSplit hlegal i
  rw [hstage] at hj
  change i.1.support ⊆
    Gamma.strictRoof
      (L.frontier
        (L.splitSuccessorStage hlegal (L.groundedInfiniteStage i)))
  simpa only [splitInfinitePath, groundedInfiniteRecordToSplit, j] using hj

/-- A target-pure path in the grounded split auxiliary preserves a selected
ladder roof along its decoded run. -/
theorem IsSplitLegal.splitGroundedTargetPure_run_terminal_mem_roof
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    (c : Stage kappa)
    (p : FinitePath (L.splitGroundedPopularAuxiliaryInput hlegal).lambda.graph)
    (hs : p.start ∈
      (L.splitGroundedPopularAuxiliaryInput hlegal).lambda.source)
    (hpure : (L.splitGroundedPopularAuxiliaryInput hlegal).IsTargetPure p)
    {x y : V}
    (hrun : PopularAuxiliary.Input.RunsFromTo x y
      ((L.splitGroundedPopularAuxiliaryInput hlegal).decodeWalkSteps p.walk))
    (hx : x ∈ Gamma.strictRoof (L.frontier c)) :
    y ∈ Gamma.roof (L.frontier c) := by
  let I := L.splitGroundedPopularAuxiliaryInput hlegal
  apply PopularAuxiliary.Input.RunsFromTo.terminal_mem_roof_of_forwardPairsRecoverStrict
      (L := I) hrun
      (R := Gamma.roof (L.frontier c))
      (Rs := Gamma.strictRoof (L.frontier c))
  · exact fun _ hz ↦ hz.1
  · exact hx.1
  · intro _ _ _
    exact hx
  · intro s hsmem hback hsEntry
    have hedge : s.edge ∈ I.familyEdges :=
      I.decodeWalkSteps_backward_on_ladder p hs hsmem hback
    have htail := hlegal.familyEdge_tail_mem_strictRoof_frontier
      c hedge (by simpa [PopularAuxiliary.Input.SignedEdge.entry, hback]
        using hsEntry)
    simpa [PopularAuxiliary.Input.SignedEdge.exit, hback] using htail
  · intro s hsmem hforward hsEntry
    have hadj : Gamma.graph.Adj s.edge.1 s.edge.2 :=
      I.decodeWalkSteps_valid p hs hsmem
    have hhead := hlegal.edge_head_mem_roof_frontier_of_tail_mem_strictRoof
      c hadj (by simpa [PopularAuxiliary.Input.SignedEdge.entry, hforward]
        using hsEntry)
    simpa [PopularAuxiliary.Input.SignedEdge.exit, hforward] using hhead
  · intro z hzRoof hzOff
    exact hlegal.mem_strictRoof_frontier_of_mem_roof_of_mem_offLadder
      c hzRoof hzOff
  · exact I.decodeWalkSteps_forwardPairsRecoverStrict p hpure

/-- Grounded finite-source gadget-exit successor-roof transport. -/
theorem IsSplitLegal.splitGroundedTargetPure_finite_gadgetExit_successorRoofTransport
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    (q : FinitePath (L.splitGroundedPopularAuxiliaryInput hlegal).lambda.graph)
    (hs : q.start ∈
      (L.splitGroundedPopularAuxiliaryInput hlegal).lambda.source)
    (hpure : (L.splitGroundedPopularAuxiliaryInput hlegal).IsTargetPure q)
    (x : L.groundedFiniteTerminalSet)
    (z : (L.splitGroundedPopularAuxiliaryInput hlegal).LV) (y : V)
    (hqx : q.start = .old x.1) (hqz : q.finish = z)
    (hzexit : (L.splitGroundedPopularAuxiliaryInput hlegal).gadgetExit z = some y) :
    y ∈ Gamma.roof
      (L.frontier (L.splitSuccessorStage hlegal (L.finiteTerminalIndex x))) := by
  let I := L.splitGroundedPopularAuxiliaryInput hlegal
  have hrun : PopularAuxiliary.Input.RunsFromTo x.1 y
      (I.decodeWalkSteps q.walk) :=
    I.decodeWalkSteps_runs_from_entry q.walk (by rw [hqx]; rfl)
      (by rw [hqz]; exact hzexit)
  exact hlegal.splitGroundedTargetPure_run_terminal_mem_roof
    (L.splitSuccessorStage hlegal (L.finiteTerminalIndex x))
      q hs hpure hrun
    (L.splitGroundedFiniteTerminal_mem_strictRoof_successorFrontier hlegal x)

/-- Grounded proxy-source gadget-exit successor-roof transport. -/
theorem IsSplitLegal.splitGroundedTargetPure_proxy_gadgetExit_successorRoofTransport
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsSplitLegal)
    (q : FinitePath (L.splitGroundedPopularAuxiliaryInput hlegal).lambda.graph)
    (hs : q.start ∈
      (L.splitGroundedPopularAuxiliaryInput hlegal).lambda.source)
    (hpure : (L.splitGroundedPopularAuxiliaryInput hlegal).IsTargetPure q)
    (i : L.groundedInfiniteRecords)
    (z : (L.splitGroundedPopularAuxiliaryInput hlegal).LV) (y : V)
    (hqi : q.start = .proxy i) (hqz : q.finish = z)
    (hzexit : (L.splitGroundedPopularAuxiliaryInput hlegal).gadgetExit z = some y) :
    y ∈ Gamma.roof
      (L.frontier
        (L.splitSuccessorStage hlegal (L.groundedInfiniteStage i))) := by
  let I := L.splitGroundedPopularAuxiliaryInput hlegal
  obtain ⟨w, hwProxy, hrun⟩ :=
    I.decodeWalkSteps_runs_from_eq_proxy q.walk hqi (by
      rw [hqz]
      exact hzexit)
  exact hlegal.splitGroundedTargetPure_run_terminal_mem_roof
    (L.splitSuccessorStage hlegal (L.groundedInfiniteStage i))
      q hs hpure hrun
    (L.splitGroundedPopularAuxiliary_proxyPath_support_subset_strictRoof
      hlegal i hwProxy)

/-- A target-pure grounded route can meet a hanging limiting component only
at an owner stage weakly below its grounded source stage. -/
theorem splitGroundedTargetPure_hangingComponentStage_le_of_gadgetExit_contact
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (p : FinitePath
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.graph)
    (hs : p.start ∈
      (L.splitGroundedPopularAuxiliaryInput hL.legal).lambda.source)
    (hpure :
      (L.splitGroundedPopularAuxiliaryInput hL.legal).IsTargetPure p)
    {Y : Gamma.DPath} (hY : Y ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma Y)
    (z : (L.splitGroundedPopularAuxiliaryInput hL.legal).LV)
    (hzp : z ∈ p.support)
    (v : V) (hvY : v ∈ Y.support)
    (hzexit :
      (L.splitGroundedPopularAuxiliaryInput hL.legal).gadgetExit z = some v) :
    L.splitHangingComponentStage hL.legal Y hY hhang ≤
      (L.splitGroundedPopularAuxiliaryIndexed hL hground).f ⟨p.start, hs⟩ := by
  let I := L.splitGroundedPopularAuxiliaryInput hL.legal
  have hmeet : p.walk.Meets ({z} : Set I.LV) :=
    ⟨z, hzp, Set.mem_singleton z⟩
  let q : FinitePath I.lambda.graph :=
    p.firstHit ({z} : Set I.LV) hmeet
  have hqStart : q.start = p.start := rfl
  have hqFinish : q.finish = z :=
    Set.mem_singleton_iff.1
      (p.firstHit_finish_mem ({z} : Set I.LV) hmeet)
  have hqSource : q.start ∈ I.lambda.source := hqStart ▸ hs
  have hqPure : I.IsTargetPure q :=
    PopularAuxiliary.Input.IsTargetPure.firstHit I hpure
      ({z} : Set I.LV) hmeet
  rcases I.start_of_mem_lambda_source p hs with
      ⟨x, hxSource, hpx⟩ | ⟨i, hpi⟩
  · let xs : L.groundedFiniteTerminalSet := ⟨x, hxSource⟩
    have hvRoof : v ∈ Gamma.roof
        (L.frontier (L.splitSuccessorStage hL.legal
          (L.finiteTerminalIndex xs))) :=
      hL.legal.splitGroundedTargetPure_finite_gadgetExit_successorRoofTransport
        q hqSource hqPure xs z v (hqStart.trans hpx) hqFinish hzexit
    have hle :=
      hL.legal.splitHangingComponentStage_le_of_support_mem_roof_successor
        (L.finiteTerminalIndex xs) hY hhang hvY hvRoof
    have hsEq :
        (⟨p.start, hs⟩ : I.lambda.source) =
          ⟨.old x, (I.mem_lambda_source_old x).2 hxSource⟩ :=
      Subtype.ext hpx
    rw [hsEq]
    exact hle
  · have hvRoof : v ∈ Gamma.roof
        (L.frontier (L.splitSuccessorStage hL.legal
          (L.groundedInfiniteStage i))) :=
      hL.legal.splitGroundedTargetPure_proxy_gadgetExit_successorRoofTransport
        q hqSource hqPure i z v (hqStart.trans hpi) hqFinish hzexit
    have hle :=
      hL.legal.splitHangingComponentStage_le_of_support_mem_roof_successor
        (L.groundedInfiniteStage i) hY hhang hvY hvRoof
    have hsEq :
        (⟨p.start, hs⟩ : I.lambda.source) =
          ⟨.proxy i, I.mem_lambda_source_proxy i⟩ :=
      Subtype.ext hpi
    rw [hsEq]
    exact hle

/-- The grounded request fan is target-pure, so every literal collision
owner satisfies the successor-correct weak chronology. -/
theorem hasSplitGroundedAssertion819WeakChronology
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    ∀ (r : PopularGroundingBridge.Request
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
      (a : Below kappa)
      (d : L.SplitGroundedAssertion819CollisionOwner hL hground S r a),
      L.splitHangingComponentStage hL.legal d.component
        d.component_mem d.component_hanging ≤ a := by
  intro r a d
  have hpure :
      (L.splitGroundedPopularAuxiliaryInput hL.legal).IsTargetPure d.path :=
    (L.splitGroundedPopularAuxiliaryInput hL.legal).requestFan_path_isTargetPure
      S r d.path_mem.1
  have hle := L.splitGroundedTargetPure_hangingComponentStage_le_of_gadgetExit_contact
    hL hground d.path
      ((PopularSwitching.restrictPaths
        (PopularGroundingBridge.requestFan S r)
        {q | GroundingConcreteControls.hangingLadderCollision
          (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut r q})
        |>.starts_in_source d.path_mem)
      hpure d.component_mem d.component_hanging d.traceContact
      d.traceContact_mem_path d.contact d.contact_mem_component d.traceContact_exit
  simpa only [d.index_eq] using hle

end KappaLadder
end DWeb
end Erdos599
