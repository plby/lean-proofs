/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawForwardProvenance
import ErdosProblems.Erdos599.DeferredGroundingSuccessorTransport
import ErdosProblems.Erdos599.LadderLimitHitClosure

/-!
# Actual deferred boundary incidences for the lossless decoder

Finite records persist unchanged to the final warp. A target marker starts
as a singleton and extends to the limiting component which contains it.
Consequently the generic raw-forward classification has no additional
boundary hypothesis for a deferred-legal ladder.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb.KappaLadder.Deferred

open _root_.Erdos599.DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A deferred ordinary-stage path meeting a final component extends to
that component. Only the geometric limit and warp fields are needed. -/
theorem IsDeferredLegal.extends_limitWarp_of_stage_intersects
    {L : Gamma.KappaLadder kappa} (hL : IsDeferredLegal L)
    {a : Ladder.Stage kappa} {q p : Gamma.DPath}
    (hq : q ∈ L.warpAt a) (hp : p ∈ L.limitWarp)
    (hqp : (q.support ∩ p.support).Nonempty) :
    Gamma.Extends q p := by
  have hkLimit : Order.IsSuccLimit kappa.ord :=
    Cardinal.isSuccLimit_ord hL.regular.aleph0_le
  obtain ⟨r, hr, hqr⟩ := hL.limitStages.grows_to_limit
    (Ladder.finalStage kappa) hkLimit ⟨a.1, a.2⟩ q hq
  obtain ⟨x, hxq, hxp⟩ := hqp
  have hrp : r = p :=
    DWeb.IsWarp.eq_of_mem_support
      (hL.warpStages (Ladder.finalStage kappa)) hr hp
      (Gamma.support_mono_of_extends hqr hxq) hxp
  rwa [hrp] at hqr

/-- A marker on a limiting deferred component is its actual initial
vertex, not merely a vertex on that component. -/
theorem IsDeferredLegal.initial_eq_of_marker_mem_limitWarp_support
    {L : Gamma.KappaLadder kappa} (hL : IsDeferredLegal L)
    {a : Ladder.Stage kappa} {y : V} (hy : L.marker a = some y)
    {p : Gamma.DPath} (hp : p ∈ L.limitWarp) (hyp : y ∈ p.support) :
    p.initial = y := by
  have htrivialSuccessor : Gamma.trivialPath y ∈ L.successorWarp a :=
    (hL.freshMarkers.2 a y hy).2
  have htrivialStage : Gamma.trivialPath y ∈
      L.warpAt (successorStage L hL a) := by
    simpa only [warpAt_successorStage] using htrivialSuccessor
  have hext : Gamma.Extends (Gamma.trivialPath y) p :=
    hL.extends_limitWarp_of_stage_intersects htrivialStage hp
      ⟨y, by simp, hyp⟩
  simpa using (Gamma.extends_initial hext).symm

/-- Every actual finite auxiliary source is terminal in the limiting
reference warp. -/
theorem finiteTerminalSet_subset_limitWarp_terminalFrontier
    (L : Gamma.KappaLadder kappa) (hL : IsDeferredLegal L) :
    finiteTerminalSet L ⊆ Gamma.terminalFrontier L.limitWarp := by
  rintro x ⟨a, _ha, p, hp, hpx⟩
  refine ⟨p, ?_, hpx⟩
  exact (L.recorded_mem_inessential hL.recordedPathsPersist hp
    (b := Ladder.finalStage kappa) (by
      change a.1 + 1 ≤ kappa.ord
      exact (Order.add_one_le_iff).2 a.2)).1

/-- Every actual target marker is an initial of the limiting reference
warp. This uses the recorded singleton's stage-to-limit continuation. -/
theorem targetMarkers_subset_limitWarp_initialSet
    (L : Gamma.KappaLadder kappa) (hL : IsDeferredLegal L) :
    (popularAuxiliaryInput L hL).targetMarkers ⊆
      Gamma.initialSet L.limitWarp := by
  rintro y ⟨⟨a, hy⟩, p, hp, hyp⟩
  exact ⟨p, hp.1, hL.initial_eq_of_marker_mem_limitWarp_support hy hp.1 hyp⟩

/-- The genuine deferred auxiliary satisfies both incidence facts used by
the raw six-arc classification, without any grounding premise. -/
theorem popularAuxiliary_hasBoundaryIncidence
    (L : Gamma.KappaLadder kappa) (hL : IsDeferredLegal L) :
    (popularAuxiliaryInput L hL).HasBoundaryIncidence := by
  constructor
  · intro x hx
    have hterminal : x ∈ Gamma.terminalFrontier L.limitWarp :=
      finiteTerminalSet_subset_limitWarp_terminalFrontier L hL hx
    have hno := not_hasOutgoing_familyEdges_of_mem_terminalFrontier_anyWarp
      (hL.warpStages (Ladder.finalStage kappa)) hterminal
    simpa only [HasOutgoing, Alternating.familyEdges,
      PopularAuxiliary.Input.familyEdges, popularAuxiliaryInput,
      Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, limitWarp] using hno
  · intro y hy
    have hinitial : y ∈ Gamma.initialSet L.limitWarp :=
      targetMarkers_subset_limitWarp_initialSet L hL hy
    have hno := not_hasIncoming_familyEdges_of_mem_initialSet_anyWarp
      (hL.warpStages (Ladder.finalStage kappa)) hinitial
    simpa only [HasIncoming, Alternating.familyEdges,
      PopularAuxiliary.Input.familyEdges, popularAuxiliaryInput,
      Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, limitWarp] using hno

/-- Concrete ordinary-source routes have no forward reference edges. -/
theorem popularAuxiliary_rawForward_disjoint_of_start_old
    (L : Gamma.KappaLadder kappa) (hL : IsDeferredLegal L)
    (p : FinitePath (popularAuxiliaryInput L hL).lambda.graph)
    (hs : p.start ∈ (popularAuxiliaryInput L hL).lambda.source)
    {x : V} (hstart : p.start = .old x) :
    Disjoint ((popularAuxiliaryInput L hL).connectorEdges p)
      (popularAuxiliaryInput L hL).familyEdges :=
  (popularAuxiliary_hasBoundaryIncidence L hL)
    |>.connectorEdges_disjoint_familyEdges_of_start_old p hs hstart

/-- The canonical raw decoder's reference-forward overlap is at most one
edge and is included in the actual backward gadgets. -/
theorem popularAuxiliary_rawForward_overlap
    (L : Gamma.KappaLadder kappa) (hL : IsDeferredLegal L)
    (p : FinitePath (popularAuxiliaryInput L hL).lambda.graph)
    (hs : p.start ∈ (popularAuxiliaryInput L hL).lambda.source) :
    (((popularAuxiliaryInput L hL).selectedConnectorEdges p ∩
      (popularAuxiliaryInput L hL).familyEdges).Subsingleton) ∧
    (popularAuxiliaryInput L hL).selectedConnectorEdges p ∩
      (popularAuxiliaryInput L hL).familyEdges ⊆
        (popularAuxiliaryInput L hL).representedEdges p := by
  have hboundary := popularAuxiliary_hasBoundaryIncidence L hL
  exact ⟨hboundary.selected_reference_subsingleton p hs,
    hboundary.selected_reference_subset_represented p hs⟩

end DWeb.KappaLadder.Deferred
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.Deferred.popularAuxiliary_hasBoundaryIncidence
#print axioms Erdos599.DWeb.KappaLadder.Deferred.popularAuxiliary_rawForward_disjoint_of_start_old
#print axioms Erdos599.DWeb.KappaLadder.Deferred.popularAuxiliary_rawForward_overlap
