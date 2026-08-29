/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingEqualCollisionInessential
import ErdosProblems.Erdos599.DeferredGroundingRawOwnerRootDescent

/-!
# Equal-stage off-apex hanging carriers are singleton markers

The selected-contact proof gives pre-marker roof membership without an
essentiality premise. That makes the newly adjoined marker singleton
inessential immediately, hence unchanged at the final limit. A contacted
hanging carrier with that initial must be the singleton. In particular
it cannot contain any actual backward edge.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Cardinal Order Set _root_.Erdos599.DirectedPath Alternating Ladder
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The refined actual deferred selector avoids its own apex owner's
entire trace away from the apex. -/
theorem reservedStrongSelectedPath_avoids_ownApexCarrier
    {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
    {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}
    (r : Request (popularAuxiliaryInput L hL.legal) S.cut) :
    Disjoint (strongSelectedPath (popularAuxiliaryIndexed L hL) S
      (reservedGroundedCarrierControls L hL S) r).support
        (GroundingApexOwnerAvoidance.offApexOwnerCarrier r) := by
  apply Set.disjoint_left.2
  intro z hzPath hzOwner
  apply strongSelectedPath_not_mem_hangingFragment (popularAuxiliaryIndexed L hL) S
    (reservedGroundedCarrierControls L hL S) r
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl ⟨z, hzPath, hzOwner⟩))))

/-- No actually changed backward owner contains the request's own apex. -/
theorem reservedRawBackwardOwner_apex_not_mem
    {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
    {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}
    (r : Request (popularAuxiliaryInput L hL.legal) S.cut)
    {Y : Gamma.DPath} (hY : Y ∈ L.limitWarp)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) (heY : e ∈ Y.edgeSet) :
    requestAuxVertex r ∉ PopularSwitching.ladderTrace
      (popularAuxiliaryInput L hL.legal) Y := by
  intro hapex
  let J := popularAuxiliaryInput L hL.legal
  have hgate := reservedRawRequestBackward_gadget r he
  have hne : LambdaVertex.edge e.1 e.2 ≠ requestAuxVertex r :=
    fun h ↦ hgate.2 (h.symm ▸ requestAuxVertex_mem_cut r)
  exact Set.disjoint_left.1 (reservedStrongSelectedPath_avoids_ownApexCarrier r)
    hgate.1 ⟨⟨Y, hY, hapex,
      (PopularSwitching.edge_mem_ladderTrace_iff J Y e.1 e.2).2 heY⟩,
      by simpa using hne⟩

/-- Any other request whose apex is on a backward-changed owner is later
in the actual selection order. Increasing rank is not a termination claim. -/
theorem reservedRawBackwardOwner_rank_lt_of_apex_mem
    {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
    {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}
    (r s : Request (popularAuxiliaryInput L hL.legal) S.cut)
    {Y : Gamma.DPath} (hY : Y ∈ L.limitWarp)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) (heY : e ∈ Y.edgeSet)
    (hapex : requestAuxVertex s ∈ PopularSwitching.ladderTrace
      (popularAuxiliaryInput L hL.legal) Y) :
    GroundingAssembly.requestRank (popularAuxiliaryIndexed L hL) S r <
      GroundingAssembly.requestRank (popularAuxiliaryIndexed L hL) S s := by
  let U := popularAuxiliaryIndexed L hL
  let K := reservedGroundedCarrierControls L hL S
  have hExpose : Y ∈ exposedLadderPaths (popularAuxiliaryInput L hL.legal)
      (strongSelectedPath U S K s) := by
    refine Or.inl ⟨hY, requestAuxVertex s, ?_, hapex⟩
    rw [← strongSelectedPath_finish U S K s]
    exact (strongSelectedPath U S K s).finish_mem_support
  rcases lt_trichotomy (GroundingAssembly.requestRank U S r)
      (GroundingAssembly.requestRank U S s) with hlt | heq | hgt
  · exact hlt
  · have hrs := (GroundingAssembly.requestRank U S).injective heq
    subst s
    exact (reservedRawBackwardOwner_apex_not_mem r hY he heY hapex).elim
  · exact (reservedRawRequestBackward_not_on_earlier_exposed s r hgt hExpose he heY).elim

/-- A marker already roofed before its insertion remains an inessential
singleton all the way to the canonical deferred limit. -/
theorem canonicalDeferredLadder_marker_singleton_persists_of_arrowRoof
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    {a : Stage kappa} {y : V}
    (hmarker : (canonicalDeferredLadder Gamma kappa preferred).marker a = some y)
    (hyRoof : y ∈ Gamma.roof (Gamma.terminalFrontier
      ((canonicalDeferredLadder Gamma kappa preferred).arrowPart a))) :
    Gamma.trivialPath y ∈ Gamma.inessentialPaths
      (canonicalDeferredLadder Gamma kappa preferred).limitWarp := by
  let L := canonicalDeferredLadder Gamma kappa preferred
  have hlegal : IsDeferredLegal L :=
    canonicalDeferredLadder_isDeferredLegal preferred hkappa huncountable hNoEnter
  have hmarkerMem : Gamma.trivialPath y ∈ L.markerPathSet a := by
    simp [markerPathSet, hmarker, L]
  have hmarkerSuccessor : Gamma.trivialPath y ∈ L.successorWarp a := by
    rw [(hlegal.exactSuccessorArrows a).2]
    exact Or.inr hmarkerMem
  have hyNotArrow : y ∉ Gamma.vertexSet (L.arrowPart a) := by
    rintro ⟨q, hqArrow, hyq⟩
    have hqSuccessor : q ∈ L.successorWarp a := by
      rw [(hlegal.exactSuccessorArrows a).2]
      exact Or.inl hqArrow
    have hqNe : q ≠ Gamma.trivialPath y :=
      fun h ↦ hqArrow.2 (h ▸ hmarkerMem)
    exact Set.disjoint_left.1
      (hlegal.warpStages (Stage.succExtended a) hqSuccessor hmarkerSuccessor hqNe)
      hyq (by simp)
  have hfrontier : Gamma.terminalFrontier (L.arrowPart a) ⊆
      Gamma.terminalFrontier (L.successorWarp a) \ {y} := by
    rintro z ⟨q, hqArrow, hqz⟩
    refine ⟨⟨q, ?_, hqz⟩, ?_⟩
    · rw [(hlegal.exactSuccessorArrows a).2]
      exact Or.inl hqArrow
    · intro hzy
      subst z
      exact hyNotArrow ⟨q, hqArrow, Gamma.terminal_mem_support hqz⟩
  have hinessential : Gamma.trivialPath y ∈
      Gamma.inessentialPaths (L.successorWarp a) := by
    refine ⟨hmarkerSuccessor, ?_⟩
    rintro ⟨_, z, hzTerminal, hzEssential⟩
    have hzy : z = y :=
      (Option.some.inj ((Gamma.terminal?_trivialPath y).symm.trans hzTerminal)).symm
    subst z
    exact hzEssential.2 (Gamma.roof_mono hfrontier hyRoof)
  exact canonicalAccumulated_inessential_mono preferred hNoEnter
    (a := Stage.succExtended a) (b := finalStage kappa)
    (by
      change a.1 + 1 ≤ kappa.ord
      exact (Order.add_one_le_iff).2 a.2) hinessential

/-- The whole off-apex hanging component is the persistent singleton at
its actual equal-stage marker, not just an arbitrary inessential path. -/
theorem canonicalDeferredLadder_selected_hangingCarrier_eq_singleton
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
    C.carrier = Gamma.trivialPath C.carrier.initial := by
  have hroof := (canonicalDeferredLadder_selected_hangingCarrier_stage_roof_inessential
    preferred hkappa huncountable hNoEnter hL S r C hmeet).2.1
  have hsingle := canonicalDeferredLadder_marker_singleton_persists_of_arrowRoof
    preferred hkappa huncountable hNoEnter C.marker_eq hroof
  exact DWeb.IsWarp.eq_of_initial_eq Gamma (hL.legal.warpStages (finalStage kappa))
    C.carrier_mem hsingle.1 (Gamma.initial_trivialPath C.carrier.initial).symm

/-- Every actual raw backward owner is grounded or contains the request
apex. There is no essential-owner assumption. -/
theorem canonicalDeferredLadder_rawBackwardOwner_grounded_or_apex
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    {Y : Gamma.DPath}
    (hY : Y ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) (heY : e ∈ Y.edgeSet) :
    Y.initial ∈ Gamma.source ∨ requestAuxVertex r ∈ PopularSwitching.ladderTrace
      (popularAuxiliaryInput (canonicalDeferredLadder Gamma kappa preferred) hL.legal) Y := by
  classical
  let L := canonicalDeferredLadder Gamma kappa preferred
  let J := popularAuxiliaryInput L hL.legal
  by_cases hground : Y.initial ∈ Gamma.source
  · exact Or.inl hground
  by_cases hapex : requestAuxVertex r ∈ PopularSwitching.ladderTrace J Y
  · exact Or.inr hapex
  obtain hsource | ⟨b, _hb, hmarker⟩ :=
    hL.legal.accumulatedInitialProvenance (finalStage kappa) Y hY
  · exact (hground hsource).elim
  let C : HangingTraceCarrier L hL S r b := {
    carrier := Y
    carrier_mem := hY
    carrier_hanging := hground
    marker_eq := hmarker
    trace_disjoint := Set.disjoint_singleton_right.2 hapex }
  have hmeet : (strongSelectedPath (popularAuxiliaryIndexed L hL) S
      (reservedGroundedCarrierControls L hL S) r).walk.Meets
        (PopularSwitching.ladderTrace J Y) := ⟨LambdaVertex.edge e.1 e.2,
    (reservedRawRequestBackward_gadget r he).1,
    (PopularSwitching.edge_mem_ladderTrace_iff J Y e.1 e.2).2 heY⟩
  have hsingle := canonicalDeferredLadder_selected_hangingCarrier_eq_singleton
    preferred hkappa huncountable hNoEnter hL S r C hmeet
  change Y = Gamma.trivialPath Y.initial at hsingle
  rw [hsingle] at heY
  change e ∈ (∅ : Set (V × V)) at heY
  exact heY.elim

/-- All actual non-cut backward changes are on genuinely source-grounded
reference owners, with no essentiality or apex exception remaining. -/
theorem canonicalDeferredLadder_rawBackwardOwner_grounded
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    {Y : Gamma.DPath}
    (hY : Y ∈ (canonicalDeferredLadder Gamma kappa preferred).limitWarp)
    {e : V × V} (he : e ∈ reservedRawRequestBackwardEdges r) (heY : e ∈ Y.edgeSet) :
    Y.initial ∈ Gamma.source := by
  rcases canonicalDeferredLadder_rawBackwardOwner_grounded_or_apex
      preferred hkappa huncountable hNoEnter hL S r hY he heY with hground | hapex
  · exact hground
  exact (reservedRawBackwardOwner_apex_not_mem r hY he heY hapex).elim

#print axioms canonicalDeferredLadder_marker_singleton_persists_of_arrowRoof
#print axioms canonicalDeferredLadder_selected_hangingCarrier_eq_singleton
#print axioms canonicalDeferredLadder_rawBackwardOwner_grounded_or_apex
#print axioms canonicalDeferredLadder_rawBackwardOwner_grounded
#print axioms reservedRawBackwardOwner_rank_lt_of_apex_mem

end Erdos599.DWeb.KappaLadder.Deferred
