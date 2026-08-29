/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingReservedSelection
import ErdosProblems.Erdos599.DeferredGroundingCanonicalPopularSeparator
import ErdosProblems.Erdos599.HalfwayDeferredReferenceRoofIncidence
import ErdosProblems.Erdos599.SplitGroundingFreshPreMarker

/-!
# Deferred equal-stage hanging collisions have inessential owners

The final deferred strong selector still carries the strict-prior collision
control.  Consequently a hanging carrier met by an actually selected route
cannot be owned at a strictly earlier stage.  Canonical pre-marker roof
geometry gives the reverse weak inequality.  At the resulting equal stage,
an essential owner would put its marker in the pre-marker arrow roof.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath Ladder Stationary
open PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The pre-marker arrow roof is contained in the deferred successor
frontier roof. -/
private theorem canonicalDeferred_arrowRoof_subset_successorFrontierRoof
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (a : Stage kappa) :
    Gamma.roof (Gamma.terminalFrontier
      ((canonicalDeferredLadder Gamma kappa preferred).arrowPart a)) ⊆
    Gamma.roof ((canonicalDeferredLadder Gamma kappa preferred).frontier
      (successorStage (canonicalDeferredLadder Gamma kappa preferred)
        (canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
          hNoEnter) a)) := by
  let L := canonicalDeferredLadder Gamma kappa preferred
  let hlegal : IsDeferredLegal L :=
    canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable
      hNoEnter
  have hsplit : (canonicalLadder Gamma kappa preferred).IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  have hsubset : Gamma.terminalFrontier (L.arrowPart a) ⊆
      Gamma.terminalFrontier (L.successorWarp a) := by
    rintro z ⟨p, hp, hpz⟩
    refine ⟨p, ?_, hpz⟩
    have hsuccessor : L.successorWarp a =
        L.arrowPart a ∪ L.markerPathSet a := by
      change (canonicalLadder Gamma kappa preferred).successorWarp a =
        (canonicalLadder Gamma kappa preferred).arrowPart a ∪
          (canonicalLadder Gamma kappa preferred).markerPathSet a
      exact (hsplit.exactSuccessorArrows a).2
    rw [hsuccessor]
    exact Or.inl hp
  intro y hy
  rw [L.frontier_eq_essential_terminalFrontier
      hlegal.roofsSourceAtStages,
    Gamma.roof_essential,
    warpAt_successorStage L hlegal]
  exact Gamma.roof_mono hsubset hy

/-- Roof membership in the canonical pre-marker arrow propagates backwards
along a limiting component. -/
private theorem canonicalDeferred_limitComponent_initial_mem_arrowRoof
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (a : Stage kappa) {p : Gamma.DPath}
    (hp : p ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp)
    {v : V} (hvp : v ∈ p.support)
    (hvRoof : v ∈ Gamma.roof (Gamma.terminalFrontier
      ((canonicalDeferredLadder Gamma kappa preferred).arrowPart a))) :
    p.initial ∈ Gamma.roof (Gamma.terminalFrontier
      ((canonicalDeferredLadder Gamma kappa preferred).arrowPart a)) := by
  let L := canonicalDeferredLadder Gamma kappa preferred
  have hback : ∀ {x y : V}, (x, y) ∈ p.edgeSet →
      y ∈ Gamma.roof (Gamma.terminalFrontier (L.arrowPart a)) →
      x ∈ Gamma.roof (Gamma.terminalFrontier (L.arrowPart a)) := by
    intro x y hxy hy
    exact (canonicalLadder_limitFamilyEdge_tail_mem_strictRoof_arrowPartFrontier
      preferred hkappa huncountable hNoEnter a ⟨p, hp, hxy⟩ hy).1
  rcases p with path | ray
  · apply Walk.start_mem_of_meets_of_backwardClosed (w := path.walk)
    · intro x y hxy hy
      exact hback hxy hy
    · exact ⟨v, hvp, hvRoof⟩
  · obtain ⟨n, hn⟩ := hvp
    subst v
    change ray 0 ∈ Gamma.roof (Gamma.terminalFrontier (L.arrowPart a))
    induction n with
    | zero => exact hvRoof
    | succ n ih =>
        apply ih
        apply hback
        · exact ⟨n, rfl⟩
        · exact hvRoof

/-- A literal meeting with a ladder trace supplies a concrete gadget exit
on the represented carrier. -/
private theorem exists_gadgetExit_contact_of_meets_ladderTrace
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (p : FinitePath J.lambda.graph) (Y : Gamma.DPath)
    (hmeet : p.walk.Meets (PopularSwitching.ladderTrace J Y)) :
    ∃ z : J.LV, ∃ v : V,
      z ∈ p.support ∧ v ∈ Y.support ∧ J.gadgetExit z = some v := by
  obtain ⟨z, hzp, hzY⟩ := hmeet
  cases z with
  | old x =>
      exact ⟨.old x, x, hzp,
        (PopularSwitching.old_mem_ladderTrace_iff J Y x).1 hzY, rfl⟩
  | edge x y =>
      have hxy : (x, y) ∈ Y.edgeSet :=
        (PopularSwitching.edge_mem_ladderTrace_iff J Y x y).1 hzY
      exact ⟨.edge x y, x, hzp, (Y.edgeSet_subset_support_prod hxy).1, rfl⟩
  | proxy i =>
      exact False.elim (PopularSwitching.proxy_not_mem_ladderTrace J Y i hzY)

/-- Every actual hanging trace carrier met by the canonical deferred final
strong selector is owned at the selected source stage and is inessential in
the limiting warp.  The hypotheses retain the literal request, selected
route, carrier, marker, trace, and trace-contact witness needed by the
subsequent rooted-cluster compiler. -/
theorem canonicalDeferredLadder_selected_hangingCarrier_stage_roof_inessential
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    {b : Stage kappa}
    (C : HangingTraceCarrier
      (canonicalDeferredLadder Gamma kappa preferred) hL S r b)
    (hmeet : (strongSelectedPath
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL)
      S (reservedGroundedCarrierControls
        (canonicalDeferredLadder Gamma kappa preferred) hL S) r).walk.Meets
      (PopularSwitching.ladderTrace
        (popularAuxiliaryInput
          (canonicalDeferredLadder Gamma kappa preferred) hL.legal)
        C.carrier)) :
    b = (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL).f
      (reservedStrongSelectedSource r) ∧
      C.carrier.initial ∈ Gamma.roof (Gamma.terminalFrontier
        ((canonicalDeferredLadder Gamma kappa preferred).arrowPart b)) ∧
      C.carrier ∈ Gamma.inessentialPaths
        (canonicalDeferredLadder Gamma kappa preferred).limitWarp := by
  let L := canonicalDeferredLadder Gamma kappa preferred
  let J := popularAuxiliaryInput L hL.legal
  let U := popularAuxiliaryIndexed L hL
  let K := reservedGroundedCarrierControls L hL S
  let p := strongSelectedPath U S K r
  let R := reservedStrongSelectedStartingRecord r
  have hpControlled := strongSelectedPath_mem_controlledRequestFan U S K r
  have hpFan : p ∈ (requestFan S r).paths := hpControlled.1.1.1
  have hpure : J.IsTargetPure p := J.requestFan_path_isTargetPure S r hpFan
  have hs : p.start ∈ J.lambda.source :=
    (requestFan S r).starts_in_source hpFan
  have hsource : (⟨p.start, hs⟩ : J.lambda.source) =
      reservedStrongSelectedSource r := Subtype.ext rfl
  have hsourceIndex : U.f ⟨p.start, hs⟩ = R.stage := by
    rw [hsource]
    rw [show U.f = auxiliarySourceIndex L hL.legal from
      (auxiliarySourceIndex_eq_sourceIndex L hL.legal).symm]
    exact R.source_index
  have hpNotPrior : p ∉ hangingLadderPaths L hL S r := by
    change strongSelectedPath U S K r ∉ hangingLadderPaths L hL S r
    simpa [K, reservedGroundedCarrierControls, reservedControlsFrom,
      groundedCarrierControls, selectionControls,
      GroundingSelection.Controls.withSourceIndexAvoidance,
      GroundingSelection.Controls.withSourceCarrierCutAvoidance] using
        (strongSelectedPath_not_mem_hangingLadder U S K r)
  obtain ⟨z, v, hzp, hvC, hzexit⟩ :=
    exists_gadgetExit_contact_of_meets_ladderTrace J p C.carrier hmeet
  have hmeetZ : p.walk.Meets ({z} : Set J.LV) :=
    ⟨z, hzp, Set.mem_singleton z⟩
  let q : FinitePath J.lambda.graph := p.firstHit ({z} : Set J.LV) hmeetZ
  have hqStart : q.start = p.start := rfl
  have hqFinish : q.finish = z :=
    Set.mem_singleton_iff.1
      (p.firstHit_finish_mem ({z} : Set J.LV) hmeetZ)
  have hqSource : q.start ∈ J.lambda.source := hqStart ▸ hs
  have hqPure : J.IsTargetPure q :=
    PopularAuxiliary.Input.IsTargetPure.firstHit J hpure ({z} : Set J.LV) hmeetZ
  have hvArrow : v ∈ Gamma.roof
      (Gamma.terminalFrontier (L.arrowPart R.stage)) := by
    rcases R.represents with ⟨f, hrecord, hsourceRep⟩ |
        ⟨i, hrecord, hsourceRep⟩
    · have hchosen : L.chosen R.stage = some (.inl f : Gamma.DPath) := by
        simpa only [hrecord] using R.chosen
      have hstart : q.start = .old f.finish := by
        exact hqStart.trans ((congrArg Subtype.val hsource).trans hsourceRep)
      have hrun : PopularAuxiliary.Input.RunsFromTo f.finish v
          (J.decodeWalkSteps q.walk) :=
        J.decodeWalkSteps_runs_from_entry q.walk
          (by rw [hstart]; rfl) (by rw [hqFinish]; exact hzexit)
      exact canonicalLadder_targetPure_run_terminal_mem_roof_arrowPartFrontier_of_ladder
        preferred hkappa huncountable hNoEnter J rfl R.stage q
          hqSource hqPure hrun
          (canonicalDeferredLadder_chosenFinite_terminal_mem_strictRoof_arrowPart
            preferred hkappa huncountable hNoEnter f hchosen)
    · obtain ⟨ray, hir⟩ := J.proxy_isRay i
      have hrecordRay : R.record = (.inr ray : Gamma.DPath) :=
        hrecord.trans hir
      have hchosen : L.chosen R.stage = some (.inr ray : Gamma.DPath) := by
        simpa only [hrecordRay] using R.chosen
      have hstart : q.start = .proxy i := by
        exact hqStart.trans ((congrArg Subtype.val hsource).trans hsourceRep)
      obtain ⟨w, hwProxy, hrun⟩ :=
        J.decodeWalkSteps_runs_from_eq_proxy q.walk hstart
          (by rw [hqFinish]; exact hzexit)
      have hwRay : w ∈ ray.support := by
        simpa only [hir, DirectedPath.Path.support] using hwProxy
      exact canonicalLadder_targetPure_run_terminal_mem_roof_arrowPartFrontier_of_ladder
        preferred hkappa huncountable hNoEnter J rfl R.stage q
          hqSource hqPure hrun
          (canonicalDeferredLadder_chosenRay_support_subset_strictRoof_arrowPart
            preferred hkappa huncountable hNoEnter ray hchosen hwRay)
  have hvSuccessor : v ∈ Gamma.roof
      (L.frontier (successorStage L hL.legal R.stage)) :=
    canonicalDeferred_arrowRoof_subset_successorFrontierRoof
      preferred hkappa huncountable hNoEnter R.stage hvArrow
  have hinitialSuccessor : C.carrier.initial ∈ Gamma.roof
      (L.frontier (successorStage L hL.legal R.stage)) :=
    limitComponent_initial_mem_roof_of_support_mem hL.legal
      (successorStage L hL.legal R.stage) C.carrier_mem hvC hvSuccessor
  have hle : b ≤ R.stage := by
    by_contra hnot
    have hab : R.stage < b := lt_of_not_ge hnot
    have hsuccle : successorStage L hL.legal R.stage ≤ b :=
      (successorStage_le_iff_lt L hL.legal).2 hab
    apply marker_not_mem_roof_frontier L hL.legal C.marker_eq
    rcases hsuccle.lt_or_eq with hlt | heq
    · exact Gamma.roof_cut (hL.legal.frontierChronology hlt) hinitialSuccessor
    · rwa [heq] at hinitialSuccessor
  have hnotlt : ¬ b < R.stage := by
    intro hlt
    let w : PriorHangingCollision L hL S r (U.f ⟨p.start, hs⟩) := {
      path := p
      path_mem := hpFan
      path_index := rfl
      stage := b
      stage_lt := by simpa only [hsourceIndex] using hlt
      traceCarrier := C
      path_meets := hmeet }
    have hwmem := mem_hangingLadderPaths_of_collision
      L hL S r (U.f ⟨p.start, hs⟩) w
    have hwpath : w.path = p := by rfl
    rw [hwpath] at hwmem
    exact hpNotPrior hwmem
  have hstage : b = R.stage := le_antisymm hle (not_lt.mp hnotlt)
  subst b
  have hindexStage : R.stage = U.f (reservedStrongSelectedSource r) := by
    exact hsourceIndex.symm.trans (congrArg U.f hsource)
  have hinitialArrow : C.carrier.initial ∈ Gamma.roof
      (Gamma.terminalFrontier (L.arrowPart R.stage)) :=
    canonicalDeferred_limitComponent_initial_mem_arrowRoof
      preferred hkappa huncountable hNoEnter R.stage C.carrier_mem hvC hvArrow
  refine ⟨hindexStage, hinitialArrow, C.carrier_mem, ?_⟩
  intro hessential
  have hmarker : L.marker R.stage = some C.carrier.initial := by
    simpa only [L] using C.marker_eq
  have hsplit : (canonicalLadder Gamma kappa preferred).IsSplitLegal :=
    canonicalLadder_isSplitLegal preferred hkappa huncountable hNoEnter
  have htarget : C.carrier.initial ∈
      ((canonicalLadder Gamma kappa preferred).splitPopularAuxiliaryInput
        hsplit).targetMarkers :=
    ⟨⟨R.stage, hmarker⟩,
      ⟨C.carrier, hessential, C.carrier.initial_mem_support⟩⟩
  exact canonicalLadder_targetMarker_not_mem_roof_arrowPartFrontier
    preferred hkappa huncountable hNoEnter hmarker htarget hinitialArrow

/-- The previous stage/inessentiality interface follows by forgetting the
now exposed pre-marker roof conclusion. -/
theorem canonicalDeferredLadder_reservedStrongSelected_hangingCarrier_stage_eq_and_inessential
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    {b : Stage kappa}
    (C : HangingTraceCarrier (canonicalDeferredLadder Gamma kappa preferred) hL S r b)
    (hmeet : (strongSelectedPath
      (popularAuxiliaryIndexed (canonicalDeferredLadder Gamma kappa preferred) hL)
      S (reservedGroundedCarrierControls
        (canonicalDeferredLadder Gamma kappa preferred) hL S) r).walk.Meets
      (PopularSwitching.ladderTrace
        (popularAuxiliaryInput (canonicalDeferredLadder Gamma kappa preferred) hL.legal)
        C.carrier)) :
    b = (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL).f
      (reservedStrongSelectedSource r) ∧
      C.carrier ∈ Gamma.inessentialPaths
        (canonicalDeferredLadder Gamma kappa preferred).limitWarp := by
  have h := canonicalDeferredLadder_selected_hangingCarrier_stage_roof_inessential
    preferred hkappa huncountable hNoEnter hL S r C hmeet
  exact ⟨h.1, h.2.2⟩

/-- The actual final deferred strong-selected route cannot meet, away from
its own request apex, the trace of an essential hanging limiting component.
This is the concrete endpoint-normalization form of the equal-stage result:
the component and its marker owner remain literal in the proof, rather than
being replaced by an abstract collision predicate. -/
theorem canonicalDeferredLadder_reservedStrongSelected_no_meets_essentialHangingCarrier
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    (Y : Gamma.DPath)
    (hY : Y ∈ (popularAuxiliaryInput
      (canonicalDeferredLadder Gamma kappa preferred) hL.legal).essentialLadder)
    (hYhanging : PopularAuxiliary.IsHangingPath Gamma Y)
    (htrace : Disjoint
      (PopularSwitching.ladderTrace
        (popularAuxiliaryInput
          (canonicalDeferredLadder Gamma kappa preferred) hL.legal) Y)
      {requestAuxVertex r}) :
    ¬ (strongSelectedPath
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL)
      S (reservedGroundedCarrierControls
        (canonicalDeferredLadder Gamma kappa preferred) hL S) r).walk.Meets
      (PopularSwitching.ladderTrace
        (popularAuxiliaryInput
          (canonicalDeferredLadder Gamma kappa preferred) hL.legal) Y) := by
  let L := canonicalDeferredLadder Gamma kappa preferred
  let J := popularAuxiliaryInput L hL.legal
  have hYessential : Y ∈ Gamma.essentialWarpPart L.limitWarp := by
    simpa only [J, popularAuxiliaryInput,
      PopularAuxiliary.Input.essentialLadder, limitWarp] using hY
  obtain hYsource | ⟨b, _hb, hmarker⟩ :=
    hL.legal.accumulatedInitialProvenance
      (Ladder.finalStage kappa) Y hYessential.1
  · exact False.elim (hYhanging hYsource)
  let C : HangingTraceCarrier L hL S r b := {
    carrier := Y
    carrier_mem := hYessential.1
    carrier_hanging := hYhanging
    marker_eq := hmarker
    trace_disjoint := htrace }
  intro hmeet
  have hout :=
    canonicalDeferredLadder_reservedStrongSelected_hangingCarrier_stage_eq_and_inessential
      preferred hkappa huncountable hNoEnter hL S r C hmeet
  exact hout.2.2 hYessential

#print axioms
  canonicalDeferredLadder_selected_hangingCarrier_stage_roof_inessential
#print axioms
  canonicalDeferredLadder_reservedStrongSelected_hangingCarrier_stage_eq_and_inessential
#print axioms
  canonicalDeferredLadder_reservedStrongSelected_no_meets_essentialHangingCarrier

end Deferred
end KappaLadder
end DWeb
end Erdos599
