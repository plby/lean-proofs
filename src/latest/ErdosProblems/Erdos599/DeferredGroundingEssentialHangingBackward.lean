/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingEqualCollisionInessential
import ErdosProblems.Erdos599.GroundingErasedRouteCore

/-!
# Backward entries into essential deferred hanging carriers

For the final deferred selector, an actual compressed backward edge on an
essential hanging limiting component can occur only when the request apex
itself belongs to that component's auxiliary trace.  Thus such an edge is an
attachment of the selected request to its essential owner, rather than an
uncontrolled off-apex collision.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath Ladder Stationary
open PopularGroundingBridge GroundingSimultaneousDecode
open Alternating PopularAuxiliary.Input GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

private theorem selectedBackwardEdge_auxContact
    {I : Type u} {J : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed J.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request J S.cut) {e : V × V}
    (he : e ∈ (selectedErasedCompression U S K r).path.directionEdges
      .backward) :
    (LambdaVertex.edge e.1 e.2 : J.LV) ∈
      (strongSelectedPath U S K r).support := by
  let T := selectedRequestTrace U S K r
  obtain ⟨s, hs, hsd, hse⟩ :=
    EndpointTrace.erasedCompression_directionEdges_subset_steps
      J T .backward he
  have hsRaw : s ∈ J.decodeWalkSteps
      (strongSelectedPath U S K r).walk :=
    (selectedRequestTrace_steps_sublist U S K r).subset hs
  have heSigned : e ∈ directedSignedEdgeSet .backward
      (J.decodeWalkSteps (strongSelectedPath U S K r).walk) :=
    ⟨s, hsRaw, hsd, hse⟩
  rw [J.backwardEdges_decodeWalkSteps
    (strongSelectedPath U S K r).walk] at heSigned
  exact heSigned

/-- Any contact of the actual final-selected auxiliary path with an
essential hanging carrier is an attachment at that request's apex.  This
is the cluster-level form: it applies before choosing a particular decoded
edge or link. -/
theorem canonicalDeferredLadder_reservedStrongSelected_meets_essentialHanging_apex_mem
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
    (hmeet : (strongSelectedPath
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL)
      S (reservedGroundedCarrierControls
        (canonicalDeferredLadder Gamma kappa preferred) hL S) r).walk.Meets
      (PopularSwitching.ladderTrace
        (popularAuxiliaryInput
          (canonicalDeferredLadder Gamma kappa preferred) hL.legal) Y)) :
    requestAuxVertex r ∈ PopularSwitching.ladderTrace
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) Y := by
  by_contra hapex
  have htrace : Disjoint
      (PopularSwitching.ladderTrace
        (popularAuxiliaryInput
          (canonicalDeferredLadder Gamma kappa preferred) hL.legal) Y)
      {requestAuxVertex r} := by
    rw [Set.disjoint_singleton_right]
    exact hapex
  exact
    (canonicalDeferredLadder_reservedStrongSelected_no_meets_essentialHangingCarrier
      preferred hkappa huncountable hNoEnter hL S r Y hY hYhanging htrace)
      hmeet

/-- An actual final-selected compressed backward edge on an essential
hanging component forces the request apex onto that component's trace. -/
theorem canonicalDeferredLadder_reservedStrongSelected_backwardEdge_on_essentialHanging_apex_mem
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
    {e : V × V}
    (heBackward : e ∈
      (selectedErasedCompression
        (popularAuxiliaryIndexed
          (canonicalDeferredLadder Gamma kappa preferred) hL)
        S (reservedGroundedCarrierControls
          (canonicalDeferredLadder Gamma kappa preferred) hL S) r).path.directionEdges
        .backward)
    (heY : e ∈ Y.edgeSet) :
    requestAuxVertex r ∈ PopularSwitching.ladderTrace
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) Y := by
  let L := canonicalDeferredLadder Gamma kappa preferred
  let J := popularAuxiliaryInput L hL.legal
  let U := popularAuxiliaryIndexed L hL
  let K := reservedGroundedCarrierControls L hL S
  by_contra hapex
  have htrace : Disjoint (PopularSwitching.ladderTrace J Y)
      {requestAuxVertex r} := by
    rw [Set.disjoint_singleton_right]
    exact hapex
  have hnotMeet :=
    canonicalDeferredLadder_reservedStrongSelected_no_meets_essentialHangingCarrier
      preferred hkappa huncountable hNoEnter hL S r Y hY hYhanging htrace
  have hePath := selectedBackwardEdge_auxContact U S K r heBackward
  apply hnotMeet
  refine ⟨LambdaVertex.edge e.1 e.2, hePath, ?_⟩
  exact Or.inr ⟨e, heY, rfl⟩

/-- Set-valued form of the attachment theorem: if the request apex is not
on the trace, the selected backward relation and the essential hanging
component are edge-disjoint. -/
theorem canonicalDeferredLadder_reservedStrongSelected_backwardEdges_disjoint_essentialHanging
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
    (hapex : requestAuxVertex r ∉ PopularSwitching.ladderTrace
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) Y) :
    Disjoint
      ((selectedErasedCompression
        (popularAuxiliaryIndexed
          (canonicalDeferredLadder Gamma kappa preferred) hL)
        S (reservedGroundedCarrierControls
          (canonicalDeferredLadder Gamma kappa preferred) hL S) r).path.directionEdges
        .backward)
      Y.edgeSet := by
  rw [Set.disjoint_left]
  intro e heBackward heY
  exact hapex
    (canonicalDeferredLadder_reservedStrongSelected_backwardEdge_on_essentialHanging_apex_mem
      preferred hkappa huncountable hNoEnter hL S r Y hY hYhanging
      heBackward heY)

/-- Native-relation form.  A backward edge deleted from an essential
hanging parent exposes the actual active request which attaches to that
parent at its own apex. -/
theorem canonicalDeferredLadder_reservedNative_backwardEdge_on_essentialHanging_exists_apexAttachment
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL))
    (T : Set V)
    (Y : Gamma.DPath)
    (hY : Y ∈ (popularAuxiliaryInput
      (canonicalDeferredLadder Gamma kappa preferred) hL.legal).essentialLadder)
    (hYhanging : PopularAuxiliary.IsHangingPath Gamma Y)
    {e : V × V}
    (heBackward : e ∈ erasedSelectedDirectionEdgesAt
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL)
      S (reservedGroundedCarrierControls
        (canonicalDeferredLadder Gamma kappa preferred) hL S) T .backward)
    (heY : e ∈ Y.edgeSet) :
    ∃ c : ActiveControlRequestAt
        (popularAuxiliaryIndexed
          (canonicalDeferredLadder Gamma kappa preferred) hL)
        S (reservedGroundedCarrierControls
          (canonicalDeferredLadder Gamma kappa preferred) hL S) T,
      e ∈ (selectedErasedCompression
        (popularAuxiliaryIndexed
          (canonicalDeferredLadder Gamma kappa preferred) hL)
        S (reservedGroundedCarrierControls
          (canonicalDeferredLadder Gamma kappa preferred) hL S)
        (chosenRequest c.1)).path.directionEdges .backward ∧
      requestAuxVertex (chosenRequest c.1) ∈ PopularSwitching.ladderTrace
        (popularAuxiliaryInput
          (canonicalDeferredLadder Gamma kappa preferred) hL.legal) Y := by
  simp only [erasedSelectedDirectionEdgesAt, Set.mem_iUnion] at heBackward
  obtain ⟨c, heBackward⟩ := heBackward
  refine ⟨c, heBackward, ?_⟩
  exact
    canonicalDeferredLadder_reservedStrongSelected_backwardEdge_on_essentialHanging_apex_mem
      preferred hkappa huncountable hNoEnter hL S (chosenRequest c.1)
      Y hY hYhanging heBackward heY

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.canonicalDeferredLadder_reservedStrongSelected_meets_essentialHanging_apex_mem
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.canonicalDeferredLadder_reservedStrongSelected_backwardEdge_on_essentialHanging_apex_mem
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.canonicalDeferredLadder_reservedStrongSelected_backwardEdges_disjoint_essentialHanging
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.canonicalDeferredLadder_reservedNative_backwardEdge_on_essentialHanging_exists_apexAttachment
